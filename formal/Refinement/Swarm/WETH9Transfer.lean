import Generated.WETH9

open FormalAst

namespace WETH9.Swarm

set_option linter.unusedSimpArgs false

/-- `transfer` reverts with "require" exactly when the sender's balance is below `wad`. -/
theorem transfer_reverts {σ : Type} (ext : WETH9.Ext σ) (dst wad : Nat) (e : Env) (w : σ)
    (h : (ext.get w).balanceOf e.sender < wad) :
    ((WETH9.transfer ext dst wad).run e).run w = .error ⟨"require"⟩ := by
  simp [WETH9.transfer, WETH9.transferFrom, h,
    ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind, Except.bind, read, ReaderT.read,
    readThe, MonadReaderOf.read, StateT.lift,
    get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift,
    pure, ReaderT.pure, StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- On success `transfer` returns `true` and writes only `balanceOf` (debit sender, then credit `dst`,
both wrapping); `allowance` is untouched because `src = msg.sender`. -/
theorem transfer_succeeds {σ : Type} (ext : WETH9.Ext σ) (dst wad : Nat) (e : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (h : wad ≤ (ext.get w).balanceOf e.sender) :
    ((WETH9.transfer ext dst wad).run e).run w =
      .ok (true, ext.set w
        (let s := ext.get w
         let b1 := upd s.balanceOf e.sender (subw 256 (s.balanceOf e.sender) wad)
         { s with balanceOf := upd b1 dst (addw 256 (b1 dst) wad) })) := by
  have h' : ¬ (ext.get w).balanceOf e.sender < wad := by omega
  simp [WETH9.transfer, WETH9.transferFrom, h', hget, hset,
    ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind, Except.bind, read, ReaderT.read,
    readThe, MonadReaderOf.read, StateT.lift,
    get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift,
    pure, ReaderT.pure, StateT.pure, Except.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Functor.map,
    StateT.map, Except.map]

end WETH9.Swarm
