import Specs.WETH9
import Proofs.Swarm.WETH9TransferFrom
import Proofs.Swarm.WETH9Conservation

open FormalAst
open WETH9

/-- S-03: a successful `transferFrom` (including `src = dst`) leaves the sum of `balanceOf`
over all 2^160 addresses unchanged. -/
theorem S03.WETH9_transferFrom {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env)
    (w w' : σ) (r : Bool)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hsA : src < 2 ^ 160) (hdA : dst < 2 ^ 160)
    (hs : (ext.get w).balanceOf src < 2 ^ 256)
    (hd : src ≠ dst → (ext.get w).balanceOf dst + wad < 2 ^ 256)
    (hok : ((WETH9.transferFrom ext src dst wad).run e).run w = .ok (r, w')) :
    WETH9.Swarm.Cons.lsum (ext.get w').balanceOf (List.range (2 ^ 160))
      = WETH9.Swarm.Cons.lsum (ext.get w).balanceOf (List.range (2 ^ 160)) :=
  WETH9.Swarm.Cons.transferFrom_conserves ext src dst wad e w hget hset _
    List.nodup_range (List.mem_range.mpr hsA) (List.mem_range.mpr hdA) hs hd r w' hok
