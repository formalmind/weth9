import Specs.WETH9
import Proofs.Swarm.WETH9TransferFrom
import Proofs.Swarm.WETH9Conservation
import Proofs.Statements.S06.WETH9Transfer

open FormalAst
open WETH9
open WETH9.Swarm.Cons

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace S06.TransferFromAux

/-- Any successful `transferFrom` leaves `balanceOf' = moveBal balanceOf src dst wad`
and requires `wad ≤ balanceOf src`. -/
theorem tf_ok {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (r : Bool) (w' : σ)
    (hok : ((WETH9.transferFrom ext src dst wad).run e).run w = .ok (r, w')) :
    wad ≤ (ext.get w).balanceOf src ∧
      (ext.get w').balanceOf = moveBal (ext.get w).balanceOf src dst wad := by
  have hg : wad ≤ (ext.get w).balanceOf src := by
    apply Nat.le_of_not_lt
    intro hc
    rw [WETH9.Swarm.TF.transferFrom_reverts_balance ext src dst wad e w hc] at hok
    cases hok
  refine ⟨hg, ?_⟩
  by_cases hn' : src = e.sender ∨ (ext.get w).allowance src e.sender = 2 ^ 256 - 1
  · rw [WETH9.Swarm.TF.transferFrom_succeeds_nospend ext src dst wad e w hget hset hg hn'] at hok
    cases hok
    rw [hget]; rfl
  · have h1 : src ≠ e.sender := fun h => hn' (Or.inl h)
    have h2 : (ext.get w).allowance src e.sender ≠ 2 ^ 256 - 1 := fun h => hn' (Or.inr h)
    by_cases ha : wad ≤ (ext.get w).allowance src e.sender
    · rw [WETH9.Swarm.TF.transferFrom_succeeds_spend ext src dst wad e w hget hset hg h1 h2 ha]
        at hok
      cases hok
      rw [hget]; rfl
    · rw [WETH9.Swarm.TF.transferFrom_reverts_allowance ext src dst wad e w hg h1 h2
        (Nat.lt_of_not_le ha)] at hok
      cases hok

end S06.TransferFromAux

open S06.TransferAux S06.TransferFromAux in
/-- S-06 for `transferFrom`: if `Σ_{a∈S} balanceOf a + forced = address(this).balance` with `S`
duplicate-free and every balance outside `S` zero, then after any successful call there is a
duplicate-free `S'` (S with `src` and `dst` added) outside which every balance is zero and
`Σ_{a∈S'} balanceOf' a + forced = address(this).balance`. `transferFrom` is nonpayable, so the
contract's balance is unchanged. -/
theorem S06.WETH9_transferFrom {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (env : Env)
    (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hbal : env.balance < 2 ^ 256)
    (forced : Nat) (S : List Nat) (hnd : S.Nodup)
    (hS : ∀ a, a ∉ S → (ext.get w).balanceOf a = 0)
    (hinv : (S.map (ext.get w).balanceOf).sum + forced = env.balance) :
    ∀ (r : Bool) (w' : σ), ((WETH9.transferFrom ext src dst wad).run env).run w = .ok (r, w') →
      ∃ S' : List Nat, S'.Nodup ∧
        (∀ a, a ∉ S' → (ext.get w').balanceOf a = 0) ∧
        (S'.map (ext.get w').balanceOf).sum + forced = env.balance := by
  intro r w' hok
  obtain ⟨hg, hpost⟩ := tf_ok ext src dst wad env w hget hset r w' hok
  rw [hpost]
  obtain ⟨b, hb⟩ : ∃ b, b = (ext.get w).balanceOf := ⟨_, rfl⟩
  rw [← hb] at hS hinv hg ⊢
  let S' := (S.insert src).insert dst
  have hn' : S'.Nodup := nodup_ins _ _ (nodup_ins _ _ hnd)
  have hsS : src ∈ S' := List.mem_insert_of_mem List.mem_insert_self
  have hdS : dst ∈ S' := List.mem_insert_self
  have hsum : lsum b S' = lsum b S := by
    simp only [S', lsum_insert]
    by_cases h1 : src ∈ S
    · by_cases h2 : dst ∈ S.insert src
      · simp [h1, h2]; try (intros; apply hS; assumption)
      · have : dst ∉ S := fun h => h2 (List.mem_insert_of_mem h)
        simp [h1, h2, hS dst this]
    · by_cases h2 : dst ∈ S.insert src
      · simp [h1, h2, hS _ h1]; try (intros; apply hS; assumption)
      · have : dst ∉ S := fun h => h2 (List.mem_insert_of_mem h)
        simp [h1, h2, hS _ h1, hS dst this]
  have hle : lsum b S' ≤ env.balance := by
    rw [hsum, lsum_eq_sum]; omega
  have hs : b src < 2 ^ 256 := by
    have := le_lsum b _ S' hsS; omega
  have hd : src ≠ dst → b dst + wad < 2 ^ 256 := by
    intro hne
    have := two_le_lsum b _ _ hne S' hn' hsS hdS; omega
  have hcons := moveBal_sum b src dst wad S' hn' hsS hdS hg hs hd
  refine ⟨S', hn', ?_, ?_⟩
  · intro a ha
    have h1 : a ≠ dst := fun h => ha (h ▸ hdS)
    have h2 : a ≠ src := fun h => ha (h ▸ hsS)
    have h3 : a ∉ S := fun h => ha (List.mem_insert_of_mem (List.mem_insert_of_mem h))
    simp [moveBal, upd, h1, h2, hS a h3]
  · rw [← lsum_eq_sum, hcons, hsum, lsum_eq_sum]; exact hinv
