import Generated.WETH9
import Refinement.Swarm.WETH9Transfer
import Refinement.Swarm.WETH9Conservation

open FormalAst
open WETH9

/-- S-03 for `transfer`: a successful call leaves the sum of `balanceOf` over all 2^160 addresses
unchanged, including `dst = msg.sender`. -/
theorem S03.WETH9_transfer {σ : Type} (ext : WETH9.Ext σ) (dst wad : Nat) (e : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hsA : e.sender < 2 ^ 160) (hdA : dst < 2 ^ 160)
    (hs : (ext.get w).balanceOf e.sender < 2 ^ 256)
    (hd : e.sender ≠ dst → (ext.get w).balanceOf dst + wad < 2 ^ 256)
    (r : Bool) (w' : σ)
    (hok : ((WETH9.transfer ext dst wad).run e).run w = Except.ok (r, w')) :
    WETH9.Swarm.Cons.lsum (ext.get w').balanceOf (List.range (2 ^ 160))
      = WETH9.Swarm.Cons.lsum (ext.get w).balanceOf (List.range (2 ^ 160)) := by
  have hg : wad ≤ (ext.get w).balanceOf e.sender := by
    apply Nat.le_of_not_lt
    intro hc
    rw [WETH9.Swarm.transfer_reverts ext dst wad e w hc] at hok
    cases hok
  rw [WETH9.Swarm.transfer_succeeds ext dst wad e w hget hset hg] at hok
  cases hok
  rw [hget]
  exact WETH9.Swarm.Cons.moveBal_sum _ e.sender dst wad _ List.nodup_range
    (List.mem_range.mpr hsA) (List.mem_range.mpr hdA) hg hs hd
