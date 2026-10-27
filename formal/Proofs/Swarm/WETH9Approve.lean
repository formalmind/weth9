import Specs.WETH9

namespace WETH9
open FormalAst

/-- `approve` never reverts; it returns `true` and writes exactly
`allowance[msg.sender][guy] := wad`, leaving every other field of storage unchanged. -/
theorem approve_spec {σ : Type} (ext : Ext σ) (guy wad : Nat) (env : Env) (w : σ) :
    ((WETH9.approve ext guy wad).run env).run w =
      .ok (true, ext.set w { ext.get w with
        allowance := upd (ext.get w).allowance env.sender
          (upd ((ext.get w).allowance env.sender) guy wad) }) := by
  rfl

/-- After `approve`, the allowance of `msg.sender` for `guy` is `wad`;
every other `(owner, spender)` entry and `balanceOf` are unchanged. -/
theorem approve_allowance {σ : Type} (ext : Ext σ) (guy wad : Nat) (env : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s) (o sp : Nat) :
    ∃ w' : σ, ((WETH9.approve ext guy wad).run env).run w = .ok (true, w') ∧
      (ext.get w').allowance o sp =
        (if o = env.sender ∧ sp = guy then wad else (ext.get w).allowance o sp) ∧
      (ext.get w').balanceOf = (ext.get w).balanceOf := by
  refine ⟨_, approve_spec ext guy wad env w, ?_, ?_⟩
  · rw [hget]
    by_cases h1 : o = env.sender <;> by_cases h2 : sp = guy <;> simp [upd, h1, h2]
  · rw [hget]

end WETH9
