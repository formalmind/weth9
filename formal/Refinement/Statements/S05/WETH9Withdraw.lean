import Generated.WETH9
import Refinement.Swarm.WETH9Withdraw
import Refinement.Statements.S01.WETH9Withdraw

open FormalAst
open WETH9

/-- S-05 for `WETH9.withdraw`: a successful `withdraw` by another account `B = env.sender ≠ A`
does not lower `balanceOf[A]` and keeps solvency (Σ balanceOf ≤ the contract's ETH), so
A can still withdraw all of its balance afterwards. `hcallA` / `hcall` describe the ETH send
(including any re-entry by other accounts): it does not lower A's balance, and preserves
solvency once `wad` has been taken out of the ledger. -/
theorem S05.WETH9_withdraw {σ : Type} (ext : WETH9.Ext σ) (wad : Nat) (env : Env) (w w' : σ)
    (A : Nat) (ethBal : σ → Nat)
    (hA : env.sender ≠ A)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hbal : ∀ w s, ethBal (ext.set w s) = ethBal w)
    (hrange : (ext.get w).balanceOf env.sender < 2 ^ 256)
    (hcallA : ∀ w1 r w2, ((ext.lowCall env.sender wad []).run env).run w1 = .ok (r, w2) →
      (ext.get w1).balanceOf A ≤ (ext.get w2).balanceOf A)
    (hcall : ∀ w1 r w2, ((ext.lowCall env.sender wad []).run env).run w1 = .ok (r, w2) →
      (∀ S : List Nat, S.Nodup → (S.map (ext.get w1).balanceOf).sum + wad ≤ ethBal w1) →
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w2).balanceOf).sum ≤ ethBal w2)
    (hinv : ∀ S : List Nat, S.Nodup → (S.map (ext.get w).balanceOf).sum ≤ ethBal w)
    (hok : ((WETH9.withdraw ext wad).run env).run w = .ok ((), w')) :
    (ext.get w).balanceOf A ≤ (ext.get w').balanceOf A ∧
    ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ ethBal w' := by
  refine ⟨?_, S01.WETH9_withdraw ext wad env w w' ethBal hget hbal hrange hcall hinv hok⟩
  by_cases hg : wad ≤ (ext.get w).balanceOf env.sender
  · rw [WETH9.withdraw_spec ext wad env w hg] at hok
    split at hok
    · cases hok
    · rename_i r w2 hc
      split at hok
      · cases hok
        have h := hcallA _ r _ hc
        rw [hget] at h
        simpa [upd_other _ _ _ _ (Ne.symm hA)] using h
      · cases hok
  · rw [WETH9.withdraw_reverts ext wad env w (by omega)] at hok
    cases hok
