import Generated.WETH9
import Refinement.Swarm.WETH9Deposit
import Refinement.Statements.S01.WETH9Deposit

open FormalAst
open WETH9

/-- S-05 for `WETH9.deposit`: a call by any account other than `A` succeeds, leaves
`balanceOf[A]` and all allowances unchanged, and preserves solvency
(Σ balanceOf ≤ contract balance), so `A` can still withdraw its whole balance. -/
theorem S05.WETH9_deposit {σ : Type} (ext : WETH9.Ext σ) (env : Env) (w : σ) (A : Nat)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hA : env.sender ≠ A)
    (hval : env.value ≤ env.balance)
    (hinv : ∀ S : List Nat, S.Nodup →
      (S.map (ext.get w).balanceOf).sum ≤ env.balance - env.value) :
    ∃ w' : σ, ((WETH9.deposit ext).run env).run w = .ok ((), w') ∧
      (ext.get w').balanceOf A = (ext.get w).balanceOf A ∧
      (ext.get w').allowance = (ext.get w).allowance ∧
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ env.balance := by
  obtain ⟨w', hrun, hsol⟩ := S01.WETH9_deposit ext env w hget hval hinv
  have hf := WETH9.deposit_frame ext env w w' hget hrun
  exact ⟨w', hrun, hf.2.1 A (Ne.symm hA), hf.2.2.1, hsol⟩
