import Specs.WETH9
import Proofs.Swarm.WETH9Approve

open FormalAst
open WETH9

/-- S-05 for `approve`: a call by any account other than `A` succeeds and leaves
`balanceOf` (hence A's balance and the sum of balances) and A's own allowances unchanged. -/
theorem S05.WETH9_approve {σ : Type} (ext : WETH9.Ext σ) (guy wad : Nat) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s) (A : Nat) (hA : env.sender ≠ A) :
    ∃ w' : σ, ((WETH9.approve ext guy wad).run env).run w = .ok (true, w') ∧
      (ext.get w').balanceOf = (ext.get w).balanceOf ∧
      (ext.get w').allowance A = (ext.get w).allowance A := by
  refine ⟨_, WETH9.approve_spec ext guy wad env w, ?_, ?_⟩
  · rw [hget]
  · rw [hget]
    simp [upd, Ne.symm hA]
