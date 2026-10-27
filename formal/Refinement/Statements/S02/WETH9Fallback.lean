import Generated.WETH9
import Refinement.Swarm.WETH9Fallback
import Refinement.Statements.S01.WETH9Fallback

open FormalAst
open WETH9

/-- S-02 for the fallback (`WETH9.«»`, which runs `deposit`): if `Σ_{a∈S} balanceOf a` is at most
the contract's ETH balance before `msg.value` arrived (`balance - value`) for every duplicate-free
list `S`, then after the call it is at most `address(this).balance`. -/
theorem S02.WETH9_ {σ : Type} (ext : WETH9.Ext σ) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hval : env.value ≤ env.balance)
    (hinv : ∀ S : List Nat, S.Nodup →
      (S.map (ext.get w).balanceOf).sum ≤ env.balance - env.value) :
    ∃ w' : σ, ((WETH9.«» ext).run env).run w = .ok ((), w') ∧
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ env.balance := by
  refine ⟨_, WETH9.fallback_spec ext env w, fun S hS => ?_⟩
  rw [hget]
  dsimp only
  have hle : addw 256 ((ext.get w).balanceOf env.sender) env.value
      ≤ (ext.get w).balanceOf env.sender + env.value := Nat.mod_le _ _
  have h1 := S01.sum_upd_le _ _ _ _ hle S hS
  have h2 := hinv S hS
  omega

/-- S-02 preservation for `WETH9.«»` (fallback): if the invariant holds before the call
(sums of balances bounded by the pre-call ETH balance), the call succeeds and the invariant
holds after it against `address(this).balance`. -/
theorem S02.WETH9_fallback {σ : Type} (ext : WETH9.Ext σ) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hval : env.value ≤ env.balance)
    (hinv : ∀ S : List Nat, S.Nodup →
      (S.map (ext.get w).balanceOf).sum ≤ env.balance - env.value) :
    ∃ w' : σ, ((WETH9.«» ext).run env).run w = .ok ((), w') ∧
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ env.balance :=
  S02.WETH9_ ext env w hget hval hinv
