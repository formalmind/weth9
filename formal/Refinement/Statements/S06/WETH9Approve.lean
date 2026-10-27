import Generated.WETH9
import Refinement.Swarm.WETH9Approve

open FormalAst
open WETH9

/-- S-06 for `approve`: the solvency relation `Σ_{a∈S} balanceOf a + forced = address(this).balance`
(with `S` a finite list of accounts outside which every balance is zero, `forced` the ghost total of
ETH forced in, and `env.balance` the contract's balance, i.e. `totalSupply()`) is preserved by every
successful call: `approve` is nonpayable, moves no ETH, and leaves `balanceOf` untouched. -/
theorem S06.WETH9_approve {σ : Type} (ext : WETH9.Ext σ) (guy wad : Nat) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s) (forced : Nat) (S : List Nat)
    (hS : ∀ a, a ∉ S → (ext.get w).balanceOf a = 0)
    (hinv : (S.map (ext.get w).balanceOf).sum + forced = env.balance) :
    ∀ (r : Bool) (w' : σ), ((WETH9.approve ext guy wad).run env).run w = .ok (r, w') →
      (∀ a, a ∉ S → (ext.get w').balanceOf a = 0) ∧
      (S.map (ext.get w').balanceOf).sum + forced = env.balance := by
  intro r w' h
  rw [WETH9.approve_spec] at h
  cases h
  rw [hget]
  exact ⟨hS, hinv⟩
