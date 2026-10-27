import Generated.WETH9
import Refinement.Swarm.WETH9Deposit
import Refinement.Statements.S06.WETH9Fallback

open FormalAst
open WETH9

/-- S-06 for `deposit`: if `Σ_{a∈S} balanceOf a + forced` equals the contract's balance before
`msg.value` arrived (`env.balance - env.value`), then after the call it equals `env.balance`
(= `totalSupply()`), and accounts outside `S` still hold zero. -/
theorem S06.WETH9_deposit {σ : Type} (ext : WETH9.Ext σ) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s) (forced : Nat) (S : List Nat)
    (hnd : S.Nodup) (hsender : env.sender ∈ S)
    (hval : env.value ≤ env.balance) (hbal : env.balance < 2 ^ 256)
    (hS : ∀ a, a ∉ S → (ext.get w).balanceOf a = 0)
    (hinv : (S.map (ext.get w).balanceOf).sum + forced = env.balance - env.value) :
    ∀ (r : Unit) (w' : σ), ((WETH9.deposit ext).run env).run w = .ok (r, w') →
      (∀ a, a ∉ S → (ext.get w').balanceOf a = 0) ∧
      (S.map (ext.get w').balanceOf).sum + forced = env.balance := by
  intro r w' h
  rw [WETH9.deposit_spec] at h
  cases h
  rw [hget]
  dsimp only
  have hle := S06.fb_le_sum_mem (ext.get w).balanceOf env.sender S hsender
  have hadd : addw 256 ((ext.get w).balanceOf env.sender) env.value
      = (ext.get w).balanceOf env.sender + env.value := by
    unfold addw; apply Nat.mod_eq_of_lt; omega
  refine ⟨fun a ha => ?_, ?_⟩
  · have hne : a ≠ env.sender := fun e => ha (e ▸ hsender)
    rw [upd_other _ _ _ _ hne]; exact hS a ha
  · rw [hadd, S06.fb_sum_upd_add _ _ _ S hnd hsender]; omega

#print axioms S06.WETH9_deposit
