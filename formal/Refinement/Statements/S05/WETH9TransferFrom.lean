import Generated.WETH9
import Refinement.Swarm.WETH9TransferFrom

open FormalAst
open WETH9

set_option linter.unusedSimpArgs false

/-- S-05 for `transferFrom`: a call by another account `e.sender ≠ A` that `A` has not
approved (`allowance[A][sender] = 0`) never lowers `balanceOf[A]`. -/
theorem S05.WETH9_transferFrom {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env)
    (w w' : σ) (r : Bool) (A : Nat)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hA : A ≠ e.sender)
    (hnoappr : (ext.get w).allowance A e.sender = 0)
    (hrangeA : (ext.get w).balanceOf A < 2 ^ 256)
    (hnoover : (ext.get w).balanceOf A + wad < 2 ^ 256)
    (hok : ((WETH9.transferFrom ext src dst wad).run e).run w = .ok (r, w')) :
    (ext.get w).balanceOf A ≤ (ext.get w').balanceOf A := by
  by_cases hb : (ext.get w).balanceOf src < wad
  · rw [WETH9.Swarm.TF.transferFrom_reverts_balance ext src dst wad e w hb] at hok
    cases hok
  have hb' : wad ≤ (ext.get w).balanceOf src := by omega
  -- If src = A, the allowance guard forces wad = 0.
  have hz : src = A → wad = 0 := by
    intro hsa
    rw [hsa] at hb' hok
    have hm : (ext.get w).allowance A e.sender ≠ 2 ^ 256 - 1 := by rw [hnoappr]; decide
    by_cases hw : wad = 0
    · exact hw
    · have ha : (ext.get w).allowance A e.sender < wad := by omega
      rw [WETH9.Swarm.TF.transferFrom_reverts_allowance ext A dst wad e w hb' hA hm ha] at hok
      cases hok
  -- Either success branch writes the same balanceOf.
  have key : (ext.get w').balanceOf =
      (let b1 := upd (ext.get w).balanceOf src (subw 256 ((ext.get w).balanceOf src) wad)
       upd b1 dst (addw 256 (b1 dst) wad)) := by
    by_cases hn : src = e.sender ∨ (ext.get w).allowance src e.sender = 2 ^ 256 - 1
    · rw [WETH9.Swarm.TF.transferFrom_succeeds_nospend ext src dst wad e w hget hset hb' hn] at hok
      cases hok; simp [hget]
    · have hs : src ≠ e.sender := fun h => hn (Or.inl h)
      have hm : (ext.get w).allowance src e.sender ≠ 2 ^ 256 - 1 := fun h => hn (Or.inr h)
      by_cases ha : (ext.get w).allowance src e.sender < wad
      · rw [WETH9.Swarm.TF.transferFrom_reverts_allowance ext src dst wad e w hb' hs hm ha] at hok
        cases hok
      rw [WETH9.Swarm.TF.transferFrom_succeeds_spend ext src dst wad e w hget hset hb' hs hm
        (by omega)] at hok
      cases hok; simp [hget]
  rw [key]
  simp only [upd, subw, addw]
  by_cases hsa : src = A
  · have h0 := hz hsa
    subst h0 hsa
    by_cases hd : src = dst
    · subst hd
      simp [Nat.add_mod_right, Nat.mod_eq_of_lt hrangeA]
    · simp [hd, Nat.add_mod_right, Nat.mod_eq_of_lt hrangeA]
  · by_cases hd : A = dst
    · subst hd
      simp [Ne.symm hsa, Nat.mod_eq_of_lt hnoover]
    · simp [hd, Ne.symm hsa]
