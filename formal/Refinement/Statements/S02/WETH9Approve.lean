import Generated.WETH9
import Refinement.Swarm.WETH9Approve

open FormalAst
open WETH9

/-- S-02 for `approve`: if `Σ_{a∈S} balanceOf a ≤ address(this).balance` holds for every
duplicate-free list of holders `S` before a successful call to `approve`, it holds after.
`approve` writes only `allowance` and moves no ETH. -/
theorem S02.WETH9_approve {σ : Type} (ext : WETH9.Ext σ) (guy wad : Nat) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hinv : ∀ S : List Nat, S.Nodup → (S.map (ext.get w).balanceOf).sum ≤ env.balance) :
    ∀ r w', ((WETH9.approve ext guy wad).run env).run w = .ok (r, w') →
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ env.balance := by
  intro r w' h S hS
  rw [WETH9.approve_spec ext guy wad env w] at h
  cases h
  rw [hget]
  exact hinv S hS
