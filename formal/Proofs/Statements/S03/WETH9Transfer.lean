import Specs.WETH9
import Proofs.Swarm.WETH9Transfer

open FormalAst
open WETH9

set_option linter.unusedSimpArgs false

namespace S03T

/-- `total f n = f 0 + f 1 + … + f (n-1)`; with `n = 2^160` it is the sum over every address. -/
def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => total f n + f n

theorem total_congr (f g : Nat → Nat) : ∀ n, (∀ a, a < n → f a = g a) → total f n = total g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [total]
    rw [total_congr f g n (fun a ha => h a (by omega)), h n (by omega)]

/-- Updating one entry k < n replaces `f k` by `v` in the total. -/
theorem total_upd (f : Nat → Nat) (k v : Nat) : ∀ n, k < n →
    total (upd f k v) n + f k = total f n + v
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [total]
    by_cases hk : k < n
    · have ih := total_upd f k v n hk
      have hn : upd f k v n = f n := by simp [upd]; omega
      rw [hn]; omega
    · have hkn : k = n := by omega
      subst hkn
      have hc := total_congr (upd f k v) f k (fun a ha => by simp [upd]; omega)
      rw [hc]; simp [upd]; omega

end S03T

/-- S-03 (transfer): a successful `transfer` leaves Σ_{a < 2^160} balanceOf a unchanged,
including when `dst = msg.sender`. -/
theorem S03.WETH9_transfer {σ : Type} (ext : WETH9.Ext σ) (dst wad : Nat) (e : Env)
    (w w' : σ) (r : Bool)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hsa : e.sender < 2 ^ 160) (hda : dst < 2 ^ 160)
    (hbal : ∀ a, (ext.get w).balanceOf a < 2 ^ 256)
    (hnoov : dst ≠ e.sender → (ext.get w).balanceOf dst + wad < 2 ^ 256)
    (hok : ((WETH9.transfer ext dst wad).run e).run w = .ok (r, w')) :
    S03T.total (ext.get w').balanceOf (2 ^ 160) = S03T.total (ext.get w).balanceOf (2 ^ 160) := by
  by_cases hb : (ext.get w).balanceOf e.sender < wad
  · rw [WETH9.Swarm.transfer_reverts ext dst wad e w hb] at hok
    cases hok
  have hb' : wad ≤ (ext.get w).balanceOf e.sender := by omega
  rw [WETH9.Swarm.transfer_succeeds ext dst wad e w hget hset hb'] at hok
  cases hok
  simp only [hget]
  have hs := hbal e.sender
  generalize (ext.get w).balanceOf = f at hs hb' hnoov ⊢
  have hsub : subw 256 (f e.sender) wad = f e.sender - wad := by
    simp only [subw]
    rw [Nat.mod_eq_of_lt (by omega : wad < 2 ^ 256)]
    have h1 : f e.sender + 2 ^ 256 - wad = (f e.sender - wad) + 2 ^ 256 := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  by_cases hd : dst = e.sender
  · rw [hd]
    have hfun : upd (upd f e.sender (subw 256 (f e.sender) wad)) e.sender
        (addw 256 (upd f e.sender (subw 256 (f e.sender) wad) e.sender) wad) = f := by
      funext x
      by_cases hx : x = e.sender
      · subst hx
        simp only [upd, ite_true, hsub, addw]
        rw [Nat.sub_add_cancel hb', Nat.mod_eq_of_lt hs]
      · simp [upd, hx]
    rw [hfun]
  · have hb1d : upd f e.sender (subw 256 (f e.sender) wad) dst = f dst := by
      simp [upd, hd]
    have hadd : addw 256 (f dst) wad = f dst + wad := by
      simp only [addw]; exact Nat.mod_eq_of_lt (hnoov hd)
    have L1 := S03T.total_upd f e.sender (subw 256 (f e.sender) wad) (2 ^ 160) hsa
    have L2 := S03T.total_upd (upd f e.sender (subw 256 (f e.sender) wad)) dst
      (addw 256 (upd f e.sender (subw 256 (f e.sender) wad) dst) wad) (2 ^ 160) hda
    rw [hb1d] at L2
    rw [hb1d]
    omega
