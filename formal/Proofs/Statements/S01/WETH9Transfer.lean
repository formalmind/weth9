import Specs.WETH9
import Proofs.Statements.S03.WETH9Transfer

open FormalAst
open WETH9

/-- S-01 for `transfer`: if Σ_{a < 2^160} balanceOf a ≤ address(this).balance before a
successful `transfer`, it holds after (the total is preserved and no ETH moves). -/
theorem S01.WETH9_transfer {σ : Type} (ext : WETH9.Ext σ) (dst wad : Nat) (e : Env)
    (w w' : σ) (r : Bool)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hsa : e.sender < 2 ^ 160) (hda : dst < 2 ^ 160)
    (hbal : ∀ a, (ext.get w).balanceOf a < 2 ^ 256)
    (hnoov : dst ≠ e.sender → (ext.get w).balanceOf dst + wad < 2 ^ 256)
    (hinv : S03T.total (ext.get w).balanceOf (2 ^ 160) ≤ e.balance)
    (hok : ((WETH9.transfer ext dst wad).run e).run w = .ok (r, w')) :
    S03T.total (ext.get w').balanceOf (2 ^ 160) ≤ e.balance := by
  rw [S03.WETH9_transfer ext dst wad e w w' r hget hset hsa hda hbal hnoov hok]
  exact hinv
