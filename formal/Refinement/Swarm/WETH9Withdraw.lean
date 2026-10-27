import Generated.WETH9

namespace WETH9
open FormalAst

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-- Guard: `withdraw` reverts with "require" when `balanceOf[msg.sender] < wad`. -/
theorem withdraw_reverts {σ : Type} (ext : Ext σ) (wad : Nat) (env : Env) (w : σ)
    (h : (ext.get w).balanceOf env.sender < wad) :
    ((WETH9.withdraw ext wad).run env).run w = .error ⟨"require"⟩ := by
  simp [WETH9.withdraw, ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind,
    pure, ReaderT.pure, StateT.pure, read, readThe, MonadReaderOf.read, ReaderT.read, get, getThe,
    MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, Except.pure, Except.bind]
  rw [if_pos h]
  rfl

/-- Success shape: under the guard, `withdraw` first sets `balanceOf[msg.sender]` to
`subw 256 bal wad` (nothing else), then calls `msg.sender` with value `wad` and empty calldata
on that updated world; it returns `()` with the call's resulting world iff the call succeeds,
reverts "transfer" if the call returns false, and propagates the call's revert. -/
theorem withdraw_spec {σ : Type} (ext : Ext σ) (wad : Nat) (env : Env) (w : σ)
    (h : wad ≤ (ext.get w).balanceOf env.sender) :
    ((WETH9.withdraw ext wad).run env).run w =
      (match ((ext.lowCall env.sender wad []).run env).run
          (ext.set w { ext.get w with
            balanceOf := upd (ext.get w).balanceOf env.sender
              (subw 256 ((ext.get w).balanceOf env.sender) wad) }) with
        | .error e => .error e
        | .ok (r, w2) => if r.1 then .ok ((), w2) else .error ⟨"transfer"⟩) := by
  simp [WETH9.withdraw, ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind,
    pure, ReaderT.pure, StateT.pure, read, readThe, MonadReaderOf.read, ReaderT.read, get, getThe,
    MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, Except.pure, Except.bind]
  rw [if_neg (by omega)]
  cases hc : ext.lowCall env.sender wad [] env
      (ext.set w { ext.get w with
        balanceOf := upd (ext.get w).balanceOf env.sender
          (subw 256 ((ext.get w).balanceOf env.sender) wad) }) with
  | error e =>
    simp only at hc
    simp [ReaderT.bind, StateT.bind, StateT.pure, StateT.get, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, ReaderT.pure, bind, pure, Except.bind, Except.pure,
      monadLift, MonadLift.monadLift, StateT.lift, liftM, hc]
  | ok p =>
    obtain ⟨⟨b, d⟩, w2⟩ := p
    simp only at hc
    cases b <;>
      simp [ReaderT.bind, StateT.bind, StateT.pure, StateT.get, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, ReaderT.pure, bind, pure, Except.bind, Except.pure,
        monadLift, MonadLift.monadLift, StateT.lift, liftM, hc] <;> rfl

/-- Arithmetic: under the guard and the uint256 range of the balance, the unchecked
subtraction does not wrap: `subw 256 bal wad = bal - wad`. -/
theorem withdraw_sub_exact (bal wad : Nat) (h : wad ≤ bal) (hb : bal < 2 ^ 256) :
    subw 256 bal wad = bal - wad := by
  have hw : wad % 2 ^ 256 = wad := Nat.mod_eq_of_lt (by omega)
  unfold subw
  rw [hw, show bal + 2 ^ 256 - wad = (bal - wad) + 2 ^ 256 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

end WETH9
