import Generated.WETH9

namespace WETH9
open FormalAst

/-- The fallback never reverts; it credits `msg.value` (mod 2^256) to `msg.sender` and writes nothing else. -/
theorem fallback_spec {σ : Type} (ext : Ext σ) (env : Env) (w : σ) :
    ((WETH9.«» ext).run env).run w =
      .ok ((), ext.set w { ext.get w with
        balanceOf := upd (ext.get w).balanceOf env.sender
          (addw 256 ((ext.get w).balanceOf env.sender) env.value) }) := by
  simp [WETH9.«», WETH9.deposit, ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind,
    pure, ReaderT.pure, StateT.pure, read, readThe, MonadReaderOf.read, ReaderT.read, get, getThe,
    MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    liftM, monadLift, MonadLift.monadLift, Except.pure, Except.bind]

/-- Frame: on success the fallback changes only `balanceOf[msg.sender]`, assuming `ext.get (ext.set w s) = s`. -/
theorem fallback_frame {σ : Type} (ext : Ext σ) (env : Env) (w w' : σ)
    (hgs : ∀ w s, ext.get (ext.set w s) = s)
    (h : ((WETH9.«» ext).run env).run w = .ok ((), w')) :
    (ext.get w').balanceOf env.sender = (addw 256 ((ext.get w).balanceOf env.sender) env.value) ∧
    (∀ a, a ≠ env.sender → (ext.get w').balanceOf a = (ext.get w).balanceOf a) ∧
    (ext.get w').allowance = (ext.get w).allowance ∧
    (ext.get w').name = (ext.get w).name ∧
    (ext.get w').symbol = (ext.get w).symbol ∧
    (ext.get w').decimals = (ext.get w).decimals := by
  rw [fallback_spec] at h
  cases h
  refine ⟨by simp [hgs, upd], fun a ha => by simp [hgs, upd, ha], by simp [hgs], by simp [hgs],
    by simp [hgs], by simp [hgs]⟩

end WETH9
