import Specs.WETH9
import Proofs.Swarm.WETH9Withdraw

open FormalAst
open WETH9

/-- Over distinct keys containing `k`, updating `f k` to `v` changes the sum by `v - f k`. -/
theorem S01.withdraw_sum_upd (f : Nat → Nat) (k v : Nat) :
    ∀ S : List Nat, S.Nodup → k ∈ S → (S.map (upd f k v)).sum + f k = (S.map f).sum + v
  | [], _, hk => by simp at hk
  | a :: t, h, hk => by
    have ht := List.nodup_cons.mp h
    by_cases hak : a = k
    · subst hak
      have : t.map (upd f a v) = t.map f := by
        apply List.map_congr_left
        intro x hx
        exact upd_other f a x v (fun e => ht.1 (e ▸ hx))
      simp only [List.map_cons, List.sum_cons, this, upd_same]
      omega
    · have hkt : k ∈ t := by
        rcases List.mem_cons.mp hk with e | e
        · exact absurd e.symm hak
        · exact e
      have ih := S01.withdraw_sum_upd f k v t ht.2 hkt
      simp only [List.map_cons, List.sum_cons, upd_other f k a v hak]
      omega

/-- If `k ∉ S`, updating `f` at `k` leaves the sum over `S` unchanged. -/
theorem S01.withdraw_sum_upd_notin (f : Nat → Nat) (k v : Nat) (S : List Nat) (hk : k ∉ S) :
    (S.map (upd f k v)).sum = (S.map f).sum := by
  congr 1
  apply List.map_congr_left
  intro x hx
  exact upd_other f k x v (fun e => hk (e ▸ hx))

/-- S-01 for `WETH9.withdraw`. `ethBal w` is the contract's ETH in world `w`; storage writes
don't change it (`hbal`). `hcall` says what the ETH send does: from a world where
Σ balanceOf + wad ≤ ethBal, a successful send of `wad` (including any re-entry) ends in a
world where Σ balanceOf ≤ ethBal. If Σ balanceOf ≤ ethBal before a successful withdraw, the
same holds afterwards. -/
theorem S01.WETH9_withdraw {σ : Type} (ext : WETH9.Ext σ) (wad : Nat) (env : Env) (w w' : σ)
    (ethBal : σ → Nat)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hbal : ∀ w s, ethBal (ext.set w s) = ethBal w)
    (hrange : (ext.get w).balanceOf env.sender < 2 ^ 256)
    (hcall : ∀ w1 r w2, ((ext.lowCall env.sender wad []).run env).run w1 = .ok (r, w2) →
      (∀ S : List Nat, S.Nodup → (S.map (ext.get w1).balanceOf).sum + wad ≤ ethBal w1) →
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w2).balanceOf).sum ≤ ethBal w2)
    (hinv : ∀ S : List Nat, S.Nodup → (S.map (ext.get w).balanceOf).sum ≤ ethBal w)
    (hok : ((WETH9.withdraw ext wad).run env).run w = .ok ((), w')) :
    ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ ethBal w' := by
  by_cases hg : wad ≤ (ext.get w).balanceOf env.sender
  · rw [WETH9.withdraw_spec ext wad env w hg] at hok
    split at hok
    · cases hok
    · rename_i r w2 hc
      split at hok
      · cases hok
        refine hcall _ r _ hc ?_
        intro S hS
        rw [hget, hbal]
        dsimp only
        rw [WETH9.withdraw_sub_exact _ _ hg hrange]
        by_cases hk : env.sender ∈ S
        · have h1 := S01.withdraw_sum_upd (ext.get w).balanceOf env.sender
            ((ext.get w).balanceOf env.sender - wad) S hS hk
          have h2 := hinv S hS
          omega
        · rw [S01.withdraw_sum_upd_notin _ _ _ S hk]
          have h2 := hinv (env.sender :: S) (List.nodup_cons.mpr ⟨hk, hS⟩)
          simp only [List.map_cons, List.sum_cons] at h2
          omega
      · cases hok
  · rw [WETH9.withdraw_reverts ext wad env w (by omega)] at hok
    cases hok
