import Generated.WETH9
import Refinement.Statements.S06.WETH9TransferFrom

open FormalAst
open WETH9
open WETH9.Swarm.Cons

/-- S-08 for `transferFrom`: after any successful call, every account other than `src` and
`dst` has the same `balanceOf` as before. -/
theorem S08.WETH9_transferFrom {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (env : Env)
    (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t) :
    ∀ (r : Bool) (w' : σ), ((WETH9.transferFrom ext src dst wad).run env).run w = .ok (r, w') →
      ∀ a, a ≠ src → a ≠ dst → (ext.get w').balanceOf a = (ext.get w).balanceOf a := by
  intro r w' hok a h1 h2
  obtain ⟨_, hpost⟩ := S06.TransferFromAux.tf_ok ext src dst wad env w hget hset r w' hok
  rw [hpost]
  simp [moveBal, upd, h1, h2]
