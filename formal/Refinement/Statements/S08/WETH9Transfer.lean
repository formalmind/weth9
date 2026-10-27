import Generated.WETH9
import Refinement.Swarm.WETH9Transfer

open FormalAst
open WETH9

/-- S-08 for `transfer`: after any successful call, every address other than the sender (`src`)
and `dst` has the same `balanceOf` as before. -/
theorem S08.WETH9_transfer {σ : Type} (ext : WETH9.Ext σ) (dst wad : Nat) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t) :
    ∀ (r : Bool) (w' : σ), ((WETH9.transfer ext dst wad).run env).run w = .ok (r, w') →
      ∀ a, a ≠ env.sender → a ≠ dst → (ext.get w').balanceOf a = (ext.get w).balanceOf a := by
  intro r w' hok a h1 h2
  have hg : wad ≤ (ext.get w).balanceOf env.sender := by
    apply Nat.le_of_not_lt
    intro hc
    rw [WETH9.Swarm.transfer_reverts ext dst wad env w hc] at hok
    cases hok
  rw [WETH9.Swarm.transfer_succeeds ext dst wad env w hget hset hg] at hok
  cases hok
  rw [hget]
  simp [upd, h1, h2]
