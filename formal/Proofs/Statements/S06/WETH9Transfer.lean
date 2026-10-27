import Specs.WETH9
import Proofs.Swarm.WETH9Transfer
import Proofs.Swarm.WETH9Conservation

open FormalAst
open WETH9
open WETH9.Swarm.Cons

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace S06.TransferAux

theorem lsum_eq_sum (f : Nat → Nat) : ∀ l : List Nat, lsum f l = (l.map f).sum
  | [] => rfl
  | a :: l => by simp [lsum, lsum_eq_sum f l]

theorem lsum_insert (f : Nat → Nat) (a : Nat) (l : List Nat) :
    lsum f (l.insert a) = lsum f l + (if a ∈ l then 0 else f a) := by
  by_cases h : a ∈ l
  · simp [List.insert_of_mem h, h]
  · simp [List.insert_of_not_mem h, h, lsum]; omega

theorem nodup_ins (a : Nat) (l : List Nat) (h : l.Nodup) : (l.insert a).Nodup := by
  by_cases ha : a ∈ l
  · rw [List.insert_of_mem ha]; exact h
  · rw [List.insert_of_not_mem ha]; exact List.nodup_cons.mpr ⟨ha, h⟩

theorem le_lsum (f : Nat → Nat) (a : Nat) : ∀ l : List Nat, a ∈ l → f a ≤ lsum f l
  | [], h => by simp at h
  | x :: l, h => by
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst h; simp [lsum]
    · have := le_lsum f a l h; simp [lsum]; omega

theorem two_le_lsum (f : Nat → Nat) (s d : Nat) (hsd : s ≠ d) (l : List Nat) (hn : l.Nodup)
    (hs : s ∈ l) (hd : d ∈ l) : f s + f d ≤ lsum f l := by
  have key := lsum_two f (fun a => if a = s ∨ a = d then 0 else f a) s d hsd
    (fun a h1 h2 => by simp [h1, h2]) l hn
  simp only [if_pos hs, if_pos hd, true_or, or_true, if_true] at key
  omega

end S06.TransferAux

open S06.TransferAux in
/-- S-06 for `transfer`: if `Σ_{a∈S} balanceOf a + forced = address(this).balance` with `S` a
duplicate-free list outside which every balance is zero, then after any successful call there is a
duplicate-free list `S'` (S with the sender and `dst` added) outside which every balance is zero and
`Σ_{a∈S'} balanceOf' a + forced = address(this).balance`. `transfer` is nonpayable, so the
contract's balance is unchanged. -/
theorem S06.WETH9_transfer {σ : Type} (ext : WETH9.Ext σ) (dst wad : Nat) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hbal : env.balance < 2 ^ 256)
    (forced : Nat) (S : List Nat) (hnd : S.Nodup)
    (hS : ∀ a, a ∉ S → (ext.get w).balanceOf a = 0)
    (hinv : (S.map (ext.get w).balanceOf).sum + forced = env.balance) :
    ∀ (r : Bool) (w' : σ), ((WETH9.transfer ext dst wad).run env).run w = .ok (r, w') →
      ∃ S' : List Nat, S'.Nodup ∧
        (∀ a, a ∉ S' → (ext.get w').balanceOf a = 0) ∧
        (S'.map (ext.get w').balanceOf).sum + forced = env.balance := by
  intro r w' hok
  have hg : wad ≤ (ext.get w).balanceOf env.sender := by
    apply Nat.le_of_not_lt
    intro hc
    rw [WETH9.Swarm.transfer_reverts ext dst wad env w hc] at hok
    cases hok
  rw [WETH9.Swarm.transfer_succeeds ext dst wad env w hget hset hg] at hok
  cases hok
  have hpost : (ext.get (ext.set w
        (let s := ext.get w
         let b1 := upd s.balanceOf env.sender (subw 256 (s.balanceOf env.sender) wad)
         { s with balanceOf := upd b1 dst (addw 256 (b1 dst) wad) }))).balanceOf
      = moveBal (ext.get w).balanceOf env.sender dst wad := by
    rw [hget]; rfl
  rw [hpost]
  obtain ⟨b, hb⟩ : ∃ b, b = (ext.get w).balanceOf := ⟨_, rfl⟩
  rw [← hb] at hS hinv hg ⊢
  let S' := (S.insert env.sender).insert dst
  have hn' : S'.Nodup := nodup_ins _ _ (nodup_ins _ _ hnd)
  have hsS : env.sender ∈ S' := List.mem_insert_of_mem List.mem_insert_self
  have hdS : dst ∈ S' := List.mem_insert_self
  have hsum : lsum b S' = lsum b S := by
    simp only [S', lsum_insert]
    by_cases h1 : env.sender ∈ S
    · by_cases h2 : dst ∈ S.insert env.sender
      · simp [h1, h2]; try (intros; apply hS; assumption)
      · have : dst ∉ S := fun h => h2 (List.mem_insert_of_mem h)
        simp [h1, h2, hS dst this]
    · by_cases h2 : dst ∈ S.insert env.sender
      · simp [h1, h2, hS _ h1]; try (intros; apply hS; assumption)
      · have : dst ∉ S := fun h => h2 (List.mem_insert_of_mem h)
        simp [h1, h2, hS _ h1, hS dst this]
  have hle : lsum b S' ≤ env.balance := by
    rw [hsum, lsum_eq_sum]; omega
  have hs : b env.sender < 2 ^ 256 := by
    have := le_lsum b _ S' hsS; omega
  have hd : env.sender ≠ dst → b dst + wad < 2 ^ 256 := by
    intro hne
    have := two_le_lsum b _ _ hne S' hn' hsS hdS; omega
  have hcons := moveBal_sum b env.sender dst wad S' hn' hsS hdS hg hs hd
  refine ⟨S', hn', ?_, ?_⟩
  · intro a ha
    have h1 : a ≠ dst := fun h => ha (h ▸ hdS)
    have h2 : a ≠ env.sender := fun h => ha (h ▸ hsS)
    have h3 : a ∉ S := fun h => ha (List.mem_insert_of_mem (List.mem_insert_of_mem h))
    simp [moveBal, upd, h1, h2, hS a h3]
  · rw [← lsum_eq_sum, hcons, hsum, lsum_eq_sum]; exact hinv
