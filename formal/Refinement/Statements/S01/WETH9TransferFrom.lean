import Generated.WETH9
import Refinement.Statements.S03.WETH9TransferFrom

open FormalAst
open WETH9

/-- S-01 for `transferFrom`: if Σ_{a < 2^160} balanceOf a ≤ address(this).balance before a
successful `transferFrom`, it holds after (the total is preserved and no ETH moves). -/
theorem S01.WETH9_transferFrom {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env)
    (w w' : σ) (r : Bool)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hsA : src < 2 ^ 160) (hdA : dst < 2 ^ 160)
    (hs : (ext.get w).balanceOf src < 2 ^ 256)
    (hd : src ≠ dst → (ext.get w).balanceOf dst + wad < 2 ^ 256)
    (hinv : WETH9.Swarm.Cons.lsum (ext.get w).balanceOf (List.range (2 ^ 160)) ≤ e.balance)
    (hok : ((WETH9.transferFrom ext src dst wad).run e).run w = .ok (r, w')) :
    WETH9.Swarm.Cons.lsum (ext.get w').balanceOf (List.range (2 ^ 160)) ≤ e.balance := by
  rw [S03.WETH9_transferFrom ext src dst wad e w w' r hget hset hsA hdA hs hd hok]
  exact hinv
