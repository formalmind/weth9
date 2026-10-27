import Generated.WETH9

open FormalAst

namespace WETH9.Swarm.TF

set_option linter.unusedSimpArgs false

/-- Guard 1: `transferFrom` reverts when `balanceOf[src] < wad`. -/
theorem transferFrom_reverts_balance {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env) (w : σ)
    (h : (ext.get w).balanceOf src < wad) :
    ((WETH9.transferFrom ext src dst wad).run e).run w = .error ⟨"require"⟩ := by
  simp [WETH9.transferFrom, h,
    ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind, Except.bind, read, ReaderT.read,
    readThe, MonadReaderOf.read, StateT.lift,
    get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift,
    pure, ReaderT.pure, StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- Guard 2: a third-party spender with a finite allowance below `wad` reverts. -/
theorem transferFrom_reverts_allowance {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env) (w : σ)
    (hb : wad ≤ (ext.get w).balanceOf src)
    (hs : src ≠ e.sender)
    (hm : (ext.get w).allowance src e.sender ≠ 2 ^ 256 - 1)
    (ha : (ext.get w).allowance src e.sender < wad) :
    ((WETH9.transferFrom ext src dst wad).run e).run w = .error ⟨"require"⟩ := by
  have hb' : ¬ (ext.get w).balanceOf src < wad := by omega
  simp [WETH9.transferFrom, hb', hs, hm, ha,
    ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind, Except.bind, read, ReaderT.read,
    readThe, MonadReaderOf.read, StateT.lift,
    get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift,
    pure, ReaderT.pure, StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- Success, spending branch: allowance is decremented, then `src` debited and `dst` credited. -/
theorem transferFrom_succeeds_spend {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hb : wad ≤ (ext.get w).balanceOf src)
    (hs : src ≠ e.sender)
    (hm : (ext.get w).allowance src e.sender ≠ 2 ^ 256 - 1)
    (ha : wad ≤ (ext.get w).allowance src e.sender) :
    ((WETH9.transferFrom ext src dst wad).run e).run w =
      .ok (true, ext.set w
        (let s := ext.get w
         let al := upd s.allowance src
           (upd (s.allowance src) e.sender (subw 256 (s.allowance src e.sender) wad))
         let b1 := upd s.balanceOf src (subw 256 (s.balanceOf src) wad)
         { s with allowance := al, balanceOf := upd b1 dst (addw 256 (b1 dst) wad) })) := by
  have hb' : ¬ (ext.get w).balanceOf src < wad := by omega
  have ha' : ¬ (ext.get w).allowance src e.sender < wad := by omega
  simp [WETH9.transferFrom, hb', ha', hs, hm, hget, hset,
    ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind, Except.bind, read, ReaderT.read,
    readThe, MonadReaderOf.read, StateT.lift,
    get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift,
    pure, ReaderT.pure, StateT.pure, Except.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Functor.map,
    StateT.map, Except.map]

/-- Success, no-spend branch (owner moves own funds, or infinite allowance):
only `balanceOf` is written; `allowance` is untouched. -/
theorem transferFrom_succeeds_nospend {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hb : wad ≤ (ext.get w).balanceOf src)
    (hn : src = e.sender ∨ (ext.get w).allowance src e.sender = 2 ^ 256 - 1) :
    ((WETH9.transferFrom ext src dst wad).run e).run w =
      .ok (true, ext.set w
        (let s := ext.get w
         let b1 := upd s.balanceOf src (subw 256 (s.balanceOf src) wad)
         { s with balanceOf := upd b1 dst (addw 256 (b1 dst) wad) })) := by
  have hb' : ¬ (ext.get w).balanceOf src < wad := by omega
  by_cases hs : src = e.sender
  · subst hs
    simp [WETH9.transferFrom, hb', hget, hset,
      ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind, Except.bind, read, ReaderT.read,
      readThe, MonadReaderOf.read, StateT.lift,
      get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift,
      pure, ReaderT.pure, StateT.pure, Except.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Functor.map,
      StateT.map, Except.map]
  · have hn : (ext.get w).allowance src e.sender = 2 ^ 256 - 1 := hn.resolve_left hs
    simp [WETH9.transferFrom, hb', hs, hn, hget, hset,
      ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind, Except.bind, read, ReaderT.read,
      readThe, MonadReaderOf.read, StateT.lift,
      get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift,
      pure, ReaderT.pure, StateT.pure, Except.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Functor.map,
      StateT.map, Except.map]

end WETH9.Swarm.TF
