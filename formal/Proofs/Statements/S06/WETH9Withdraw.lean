import Specs.WETH9
import Proofs.Swarm.WETH9Withdraw
import Proofs.Statements.S06.WETH9Fallback

open FormalAst
open WETH9

/-- Over a duplicate-free list containing `k`, lowering `f k` by `d ≤ f k` lowers the sum by `d`. -/
theorem S06.wd_sum_upd_sub (f : Nat → Nat) (k d : Nat) (S : List Nat) (hnd : S.Nodup)
    (hk : k ∈ S) (hd : d ≤ f k) :
    (S.map (upd f k (f k - d))).sum + d = (S.map f).sum := by
  have hfg : f = upd (upd f k (f k - d)) k (upd f k (f k - d) k + d) := by
    funext x
    by_cases hx : x = k
    · subst hx; rw [upd_same, upd_same]; omega
    · rw [upd_other _ _ _ _ hx, upd_other _ _ _ _ hx]
  have hsum := S06.fb_sum_upd_add (upd f k (f k - d)) k d S hnd hk
  rw [← hfg] at hsum
  omega

/-- S-06 for `withdraw`: if `Σ_{a∈S} balanceOf a + forced = env.balance` (the contract's balance,
`totalSupply()`) before the call, then after a successful call it equals `env.balance - wad`, the
contract's balance once `wad` wei have been sent to `msg.sender` (and `wad ≤ env.balance`). The send
is opaque: it is assumed (`hcall`) that a successful send leaves `balanceOf` as it found it
(re-entry nets out). -/
theorem S06.WETH9_withdraw {σ : Type} (ext : WETH9.Ext σ) (wad : Nat) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s) (forced : Nat) (S : List Nat)
    (hnd : S.Nodup) (hsender : env.sender ∈ S)
    (hrange : (ext.get w).balanceOf env.sender < 2 ^ 256)
    (hcall : ∀ (w1 w2 : σ) r, ((ext.lowCall env.sender wad []).run env).run w1 = .ok (r, w2) →
      (ext.get w2).balanceOf = (ext.get w1).balanceOf)
    (hS : ∀ a, a ∉ S → (ext.get w).balanceOf a = 0)
    (hinv : (S.map (ext.get w).balanceOf).sum + forced = env.balance) :
    ∀ (r : Unit) (w' : σ), ((WETH9.withdraw ext wad).run env).run w = .ok (r, w') →
      (∀ a, a ∉ S → (ext.get w').balanceOf a = 0) ∧
      (S.map (ext.get w').balanceOf).sum + forced = env.balance - wad ∧ wad ≤ env.balance := by
  intro r w' h
  by_cases hg : wad ≤ (ext.get w).balanceOf env.sender
  · rw [WETH9.withdraw_spec ext wad env w hg] at h
    split at h
    · cases h
    · rename_i p w2 hc
      split at h
      · cases h
        have hb := hcall _ _ _ hc
        rw [hb, hget]
        dsimp only
        rw [WETH9.withdraw_sub_exact _ _ hg hrange]
        have hsum := S06.wd_sum_upd_sub (ext.get w).balanceOf env.sender wad S hnd hsender hg
        refine ⟨fun a ha => ?_, by omega, by omega⟩
        have hne : a ≠ env.sender := fun e => ha (e ▸ hsender)
        rw [upd_other _ _ _ _ hne]; exact hS a ha
      · cases h
  · rw [WETH9.withdraw_reverts ext wad env w (by omega)] at h; cases h

#print axioms S06.WETH9_withdraw
