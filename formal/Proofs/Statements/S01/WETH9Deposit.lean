import Specs.WETH9
import Proofs.Swarm.WETH9Deposit

open FormalAst
open WETH9

/-- Updating `f` at `k` to a value at most `f k + d` raises a sum over distinct keys by at most `d`. -/
theorem S01.deposit_sum_upd_le (f : Nat → Nat) (k v d : Nat) (hv : v ≤ f k + d) :
    ∀ S : List Nat, S.Nodup → (S.map (upd f k v)).sum ≤ (S.map f).sum + d
  | [], _ => by simp
  | a :: t, h => by
    have ht := (List.nodup_cons.mp h)
    by_cases hak : a = k
    · subst hak
      have : t.map (upd f a v) = t.map f := by
        apply List.map_congr_left
        intro x hx
        exact upd_other f a x v (fun e => ht.1 (e ▸ hx))
      simp only [List.map_cons, List.sum_cons, this, upd_same]
      omega
    · have ih := S01.deposit_sum_upd_le f k v d hv t ht.2
      simp only [List.map_cons, List.sum_cons, upd_other f k a v hak]
      omega

/-- S-01 for `WETH9.deposit`: if Σ balanceOf ≤ balance before `msg.value` arrived,
then after the call Σ balanceOf ≤ the contract's balance. -/
theorem S01.WETH9_deposit {σ : Type} (ext : WETH9.Ext σ) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hval : env.value ≤ env.balance)
    (hinv : ∀ S : List Nat, S.Nodup →
      (S.map (ext.get w).balanceOf).sum ≤ env.balance - env.value) :
    ∃ w' : σ, ((WETH9.deposit ext).run env).run w = .ok ((), w') ∧
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ env.balance := by
  refine ⟨_, WETH9.deposit_spec ext env w, fun S hS => ?_⟩
  rw [hget]
  dsimp only
  have hle : addw 256 ((ext.get w).balanceOf env.sender) env.value
      ≤ (ext.get w).balanceOf env.sender + env.value := Nat.mod_le _ _
  have h1 := S01.deposit_sum_upd_le _ _ _ _ hle S hS
  have h2 := hinv S hS
  omega
