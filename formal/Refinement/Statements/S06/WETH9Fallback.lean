import Generated.WETH9
import Refinement.Swarm.WETH9Fallback

open FormalAst
open WETH9

/-- A member's term is at most the sum. -/
theorem S06.fb_le_sum_mem (f : Nat → Nat) (k : Nat) :
    ∀ S : List Nat, k ∈ S → f k ≤ (S.map f).sum
  | [], hk => by simp at hk
  | a :: t, hk => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hk with e | e
    · subst e; omega
    · have := S06.fb_le_sum_mem f k t e; omega

/-- Over a duplicate-free list containing `k`, raising `f k` by `d` raises the sum by exactly `d`. -/
theorem S06.fb_sum_upd_add (f : Nat → Nat) (k d : Nat) :
    ∀ S : List Nat, S.Nodup → k ∈ S → (S.map (upd f k (f k + d))).sum = (S.map f).sum + d
  | [], _, hk => by simp at hk
  | a :: t, h, hk => by
    have ht := (List.nodup_cons.mp h)
    by_cases hak : a = k
    · subst hak
      have : t.map (upd f a (f a + d)) = t.map f := by
        apply List.map_congr_left
        intro x hx
        exact upd_other f a x _ (fun e => ht.1 (e ▸ hx))
      simp only [List.map_cons, List.sum_cons, this, upd_same]
      omega
    · have hkt : k ∈ t := by
        rcases List.mem_cons.mp hk with e | e
        · exact absurd e.symm hak
        · exact e
      have ih := S06.fb_sum_upd_add f k d t ht.2 hkt
      simp only [List.map_cons, List.sum_cons, upd_other f k a _ hak]
      omega

/-- S-06 for the fallback (`WETH9.«»`, which runs `deposit`): if `Σ_{a∈S} balanceOf a + forced`
equals the contract's balance before `msg.value` arrived (`env.balance - env.value`), then after the
call it equals `env.balance` (= `totalSupply()`). -/
theorem S06.WETH9_ {σ : Type} (ext : WETH9.Ext σ) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s) (forced : Nat) (S : List Nat)
    (hnd : S.Nodup) (hsender : env.sender ∈ S)
    (hval : env.value ≤ env.balance) (hbal : env.balance < 2 ^ 256)
    (hS : ∀ a, a ∉ S → (ext.get w).balanceOf a = 0)
    (hinv : (S.map (ext.get w).balanceOf).sum + forced = env.balance - env.value) :
    ∀ (r : Unit) (w' : σ), ((WETH9.«» ext).run env).run w = .ok (r, w') →
      (∀ a, a ∉ S → (ext.get w').balanceOf a = 0) ∧
      (S.map (ext.get w').balanceOf).sum + forced = env.balance := by
  intro r w' h
  rw [WETH9.fallback_spec] at h
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

#print axioms S06.WETH9_
