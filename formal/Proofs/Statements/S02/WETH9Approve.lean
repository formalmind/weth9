import Specs.WETH9
import Proofs.Swarm.WETH9Approve

open FormalAst
open WETH9

/-- S-02 for `approve`: if `Σ_{a∈S} balanceOf a ≤ address(this).balance` for every duplicate-free
list of holders `S` before a call to `WETH9.approve`, it holds after (the call always succeeds,
writes only `allowance`, and moves no ETH). -/
theorem S02.WETH9_approve {σ : Type} (ext : WETH9.Ext σ) (guy wad : Nat) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hinv : ∀ S : List Nat, S.Nodup → (S.map (ext.get w).balanceOf).sum ≤ env.balance) :
    ∃ w' : σ, ((WETH9.approve ext guy wad).run env).run w = .ok (true, w') ∧
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ env.balance := by
  refine ⟨_, WETH9.approve_spec ext guy wad env w, fun S hS => ?_⟩
  rw [hget]
  exact hinv S hS
