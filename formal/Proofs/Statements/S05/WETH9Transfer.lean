import Specs.WETH9
import Proofs.Swarm.WETH9Transfer

open FormalAst
open WETH9

set_option linter.unusedSimpArgs false

/-- S-05 for `transfer`: a call by any account other than `A` either reverts (state unchanged)
or succeeds without lowering `balanceOf A` and without touching A's allowances; it sends no ETH,
so A's later `withdraw(balanceOf A)` is unaffected. -/
theorem S05.WETH9_transfer {σ : Type} (ext : WETH9.Ext σ) (dst wad : Nat) (e : Env)
    (w w' : σ) (r : Bool)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (A : Nat) (hA : e.sender ≠ A)
    (hnoov : (ext.get w).balanceOf A + wad < 2 ^ 256)
    (hok : ((WETH9.transfer ext dst wad).run e).run w = .ok (r, w')) :
    (ext.get w).balanceOf A ≤ (ext.get w').balanceOf A ∧
      (ext.get w').allowance A = (ext.get w).allowance A := by
  by_cases hb : (ext.get w).balanceOf e.sender < wad
  · rw [WETH9.Swarm.transfer_reverts ext dst wad e w hb] at hok
    cases hok
  rw [WETH9.Swarm.transfer_succeeds ext dst wad e w hget hset (by omega)] at hok
  cases hok
  refine ⟨?_, by simp only [hget]⟩
  simp only [hget]
  by_cases hd : dst = A
  · subst hd
    simp only [upd, addw, Ne.symm hA, ite_false, ite_true]
    rw [Nat.mod_eq_of_lt hnoov]; omega
  · simp [upd, Ne.symm hA, Ne.symm hd]
