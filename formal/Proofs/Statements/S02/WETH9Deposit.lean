import Specs.WETH9
import Proofs.Swarm.WETH9Deposit
import Proofs.Statements.S01.WETH9Deposit

open FormalAst
open WETH9

/-- S-02 for `WETH9.deposit`: if Σ balanceOf ≤ totalSupply before `msg.value` arrived
(`env.balance - env.value`), then after the call Σ balanceOf ≤ totalSupply (`env.balance`). -/
theorem S02.WETH9_deposit {σ : Type} (ext : WETH9.Ext σ) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hval : env.value ≤ env.balance)
    (hinv : ∀ S : List Nat, S.Nodup →
      (S.map (ext.get w).balanceOf).sum ≤ env.balance - env.value) :
    ∃ w' : σ, ((WETH9.deposit ext).run env).run w = .ok ((), w') ∧
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ env.balance :=
  S01.WETH9_deposit ext env w hget hval hinv
