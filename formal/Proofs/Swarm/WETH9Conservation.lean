import Specs.WETH9
import Proofs.Swarm.WETH9TransferFrom

open FormalAst

namespace WETH9.Swarm.Cons

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-- Sum of `f` over a list of accounts. -/
def lsum (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | a :: l => f a + lsum f l

/-- Two maps that agree off `{s, d}` (`s ≠ d`): sums over a duplicate-free list differ only by
the `s` and `d` terms of the list. -/
theorem lsum_two (f g : Nat → Nat) (s d : Nat) (hsd : s ≠ d)
    (hoff : ∀ a, a ≠ s → a ≠ d → f a = g a) :
    ∀ l : List Nat, l.Nodup →
      lsum f l + (if s ∈ l then g s else 0) + (if d ∈ l then g d else 0)
        = lsum g l + (if s ∈ l then f s else 0) + (if d ∈ l then f d else 0)
  | [], _ => by simp [lsum]
  | x :: l, hn => by
    have hx : x ∉ l := (List.nodup_cons.mp hn).1
    have ih := lsum_two f g s d hsd hoff l (List.nodup_cons.mp hn).2
    simp only [lsum, List.mem_cons]
    by_cases h1 : x = s
    · subst h1
      have hd' : (d = x ∨ d ∈ l) ↔ d ∈ l := by
        constructor
        · rintro (h | h)
          · exact absurd h.symm hsd
          · exact h
        · exact Or.inr
      simp only [true_or, if_true, hd', if_neg hx] at ih ⊢
      omega
    · by_cases h2 : x = d
      · subst h2
        have hs' : (s = x ∨ s ∈ l) ↔ s ∈ l := by
          constructor
          · rintro (h | h)
            · exact absurd h hsd
            · exact h
          · exact Or.inr
        simp only [true_or, if_true, hs', if_neg hx] at ih ⊢
        omega
      · have hs' : (s = x ∨ s ∈ l) ↔ s ∈ l := by
          constructor
          · rintro (h | h)
            · exact absurd h.symm h1
            · exact h
          · exact Or.inr
        have hd' : (d = x ∨ d ∈ l) ↔ d ∈ l := by
          constructor
          · rintro (h | h)
            · exact absurd h.symm h2
            · exact h
          · exact Or.inr
        simp only [hs', hd']
        rw [hoff x h1 h2]
        omega

theorem lsum_congr (f g : Nat → Nat) (h : ∀ a, f a = g a) : ∀ l, lsum f l = lsum g l
  | [] => rfl
  | a :: l => by simp [lsum, h a, lsum_congr f g h l]

/-- The balance update `transferFrom`/`transfer` performs: debit `src`, then credit `dst`. -/
def moveBal (b : Nat → Nat) (src dst wad : Nat) : Nat → Nat :=
  let b1 := upd b src (subw 256 (b src) wad)
  upd b1 dst (addw 256 (b1 dst) wad)

/-- S-03 core: the move conserves the sum of balances over any duplicate-free list of accounts
holding `src` and `dst`, including `src = dst`, when the guard holds and nothing wraps. -/
theorem moveBal_sum (b : Nat → Nat) (src dst wad : Nat) (l : List Nat) (hn : l.Nodup)
    (hsA : src ∈ l) (hdA : dst ∈ l)
    (hg : wad ≤ b src) (hs : b src < 2 ^ 256)
    (hd : src ≠ dst → b dst + wad < 2 ^ 256) :
    lsum (moveBal b src dst wad) l = lsum b l := by
  have hsub : subw 256 (b src) wad = b src - wad := by
    have hw : wad % 2 ^ 256 = wad := Nat.mod_eq_of_lt (by omega)
    unfold subw
    rw [hw, show b src + 2 ^ 256 - wad = (b src - wad) + 2 ^ 256 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  by_cases h : src = dst
  · subst h
    apply lsum_congr
    intro a
    by_cases ha : a = src
    · subst ha
      simp [moveBal, upd, hsub, addw, Nat.sub_add_cancel hg, Nat.mod_eq_of_lt hs]
    · simp [moveBal, upd, ha]
  · have key := lsum_two (moveBal b src dst wad) b src dst h
      (fun a h1 h2 => by simp [moveBal, upd, h1, h2]) l hn
    have e1 : moveBal b src dst wad src = b src - wad := by
      simp [moveBal, upd, h, hsub]
    have e2 : moveBal b src dst wad dst = b dst + wad := by
      simp only [moveBal, upd, if_pos rfl, if_neg (Ne.symm h), addw]
      exact Nat.mod_eq_of_lt (hd h)
    simp only [if_pos hsA, if_pos hdA, e1, e2] at key
    omega

/-- S-03 for `transferFrom`: whenever it succeeds (either branch), the sum of `balanceOf` over
any duplicate-free list of accounts holding `src` and `dst` is unchanged. -/
theorem transferFrom_conserves {σ : Type} (ext : WETH9.Ext σ) (src dst wad : Nat) (e : Env) (w : σ)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hset : ∀ w s t, ext.set (ext.set w s) t = ext.set w t)
    (l : List Nat) (hn : l.Nodup) (hsA : src ∈ l) (hdA : dst ∈ l)
    (hs : (ext.get w).balanceOf src < 2 ^ 256)
    (hd : src ≠ dst → (ext.get w).balanceOf dst + wad < 2 ^ 256)
    (r : Bool) (w' : σ)
    (hok : ((WETH9.transferFrom ext src dst wad).run e).run w = .ok (r, w')) :
    lsum (ext.get w').balanceOf l = lsum (ext.get w).balanceOf l := by
  have hg : wad ≤ (ext.get w).balanceOf src := by
    apply Nat.le_of_not_lt
    intro hc
    rw [WETH9.Swarm.TF.transferFrom_reverts_balance ext src dst wad e w hc] at hok
    cases hok
  by_cases hn' : src = e.sender ∨ (ext.get w).allowance src e.sender = 2 ^ 256 - 1
  · rw [WETH9.Swarm.TF.transferFrom_succeeds_nospend ext src dst wad e w hget hset hg hn'] at hok
    cases hok
    rw [hget]
    exact moveBal_sum _ src dst wad l hn hsA hdA hg hs hd
  · have h1 : src ≠ e.sender := fun h => hn' (Or.inl h)
    have h2 : (ext.get w).allowance src e.sender ≠ 2 ^ 256 - 1 := fun h => hn' (Or.inr h)
    by_cases ha : wad ≤ (ext.get w).allowance src e.sender
    · rw [WETH9.Swarm.TF.transferFrom_succeeds_spend ext src dst wad e w hget hset hg h1 h2 ha]
        at hok
      cases hok
      rw [hget]
      exact moveBal_sum _ src dst wad l hn hsA hdA hg hs hd
    · rw [WETH9.Swarm.TF.transferFrom_reverts_allowance ext src dst wad e w hg h1 h2
        (Nat.lt_of_not_le ha)] at hok
      cases hok

end WETH9.Swarm.Cons
