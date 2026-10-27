import Generated.WETH9
import Refinement.Swarm.WETH9TransferFrom

open FormalAst
open WETH9

set_option linter.unusedSimpArgs false

/-- S-04: a successful third-party `transferFrom` required `allowance[src][sender] ≥ wad`
beforehand and leaves it decreased by exactly `wad`, unless it was `2^256 - 1` (unchanged). -/
theorem S04.WETH9_transferFrom {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env)
    (w w' : σ) (r : Bool)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (hs : src ≠ e.sender) (_hd : src ≠ dst) (_hpos : 0 < wad)
    (hwad : wad < 2 ^ 256)
    (hrange : (ext.get w).allowance src e.sender < 2 ^ 256)
    (hok : ((WETH9.transferFrom ext src dst wad).run e).run w = .ok (r, w')) :
    wad ≤ (ext.get w).allowance src e.sender ∧
    (ext.get w').allowance src e.sender =
      (if (ext.get w).allowance src e.sender = 2 ^ 256 - 1
       then (ext.get w).allowance src e.sender
       else (ext.get w).allowance src e.sender - wad) := by
  by_cases hb : (ext.get w).balanceOf src < wad
  · rw [WETH9.Swarm.TF.transferFrom_reverts_balance ext src dst wad e w hb] at hok
    cases hok
  have hb' : wad ≤ (ext.get w).balanceOf src := by omega
  by_cases hm : (ext.get w).allowance src e.sender = 2 ^ 256 - 1
  · rw [WETH9.Swarm.TF.transferFrom_succeeds_nospend ext src dst wad e w hget hset hb'
      (Or.inr hm)] at hok
    cases hok
    refine ⟨by omega, ?_⟩
    simp [hget, hm]
  · by_cases ha : (ext.get w).allowance src e.sender < wad
    · rw [WETH9.Swarm.TF.transferFrom_reverts_allowance ext src dst wad e w hb' hs hm ha] at hok
      cases hok
    have ha' : wad ≤ (ext.get w).allowance src e.sender := by omega
    rw [WETH9.Swarm.TF.transferFrom_succeeds_spend ext src dst wad e w hget hset hb' hs hm ha']
      at hok
    cases hok
    refine ⟨ha', ?_⟩
    simp only [hget, upd, hm, subw]
    rw [Nat.mod_eq_of_lt hwad]
    have h1 : (ext.get w).allowance src e.sender + 2 ^ 256 - wad =
        ((ext.get w).allowance src e.sender - wad) + 2 ^ 256 := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [upd]
