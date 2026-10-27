import Specs.WETH9
import Proofs.Swarm.WETH9Fallback
import Proofs.Statements.S01.WETH9Fallback

open FormalAst
open WETH9

/-- S-05 for the fallback (`WETH9.«»`): a call by any account other than `A` succeeds, leaves
A's balance and all allowances unchanged, and preserves solvency (sum of balances ≤ ETH held). -/
theorem S05.WETH9_ {σ : Type} (ext : WETH9.Ext σ) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s) (A : Nat) (hA : env.sender ≠ A)
    (hinv : ∀ S : List Nat, S.Nodup →
      (S.map (ext.get w).balanceOf).sum ≤ env.balance - env.value)
    (hval : env.value ≤ env.balance) :
    ∃ w' : σ, ((WETH9.«» ext).run env).run w = .ok ((), w') ∧
      (ext.get w').balanceOf A = (ext.get w).balanceOf A ∧
      (ext.get w').allowance = (ext.get w).allowance ∧
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ env.balance := by
  obtain ⟨w', h, hS⟩ := S01.WETH9_ ext env w hget hval hinv
  refine ⟨w', h, ?_, ?_, hS⟩
  · exact (WETH9.fallback_frame ext env w w' hget h).2.1 A (Ne.symm hA)
  · exact (WETH9.fallback_frame ext env w w' hget h).2.2.1

/-- S-05, fallback: a fallback call by another account cannot break A's ability to withdraw all:
it succeeds, leaves `balanceOf[A]` and every allowance untouched, and keeps solvency. -/
theorem S05.WETH9_fallback {σ : Type} (ext : WETH9.Ext σ) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s) (A : Nat) (hA : env.sender ≠ A)
    (hinv : ∀ S : List Nat, S.Nodup →
      (S.map (ext.get w).balanceOf).sum ≤ env.balance - env.value)
    (hval : env.value ≤ env.balance) :
    ∃ w' : σ, ((WETH9.«» ext).run env).run w = .ok ((), w') ∧
      (ext.get w').balanceOf A = (ext.get w).balanceOf A ∧
      (ext.get w').allowance = (ext.get w).allowance ∧
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ env.balance :=
  S05.WETH9_ ext env w hget A hA hinv hval
