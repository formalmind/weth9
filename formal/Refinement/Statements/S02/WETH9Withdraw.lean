import Generated.WETH9
import Refinement.Swarm.WETH9Withdraw
import Refinement.Statements.S01.WETH9Withdraw

open FormalAst
open WETH9

/-- S-02 for `WETH9.withdraw`: if Σ balanceOf ≤ the contract's ETH balance (`ethBal`, i.e.
`totalSupply()`) over every finite set of distinct accounts before a successful withdraw,
it holds afterwards. Storage writes leave `ethBal` unchanged (`hbal`); the ETH send
(with any re-entry) takes a world with Σ balanceOf + wad ≤ ethBal to one with Σ ≤ ethBal
(`hcall`). -/
theorem S02.WETH9_withdraw {σ : Type} (ext : WETH9.Ext σ) (wad : Nat) (env : Env) (w w' : σ)
    (ethBal : σ → Nat)
    (hget : ∀ w s, ext.get (ext.set w s) = s)
    (hbal : ∀ w s, ethBal (ext.set w s) = ethBal w)
    (hrange : (ext.get w).balanceOf env.sender < 2 ^ 256)
    (hcall : ∀ w1 r w2, ((ext.lowCall env.sender wad []).run env).run w1 = .ok (r, w2) →
      (∀ S : List Nat, S.Nodup → (S.map (ext.get w1).balanceOf).sum + wad ≤ ethBal w1) →
      ∀ S : List Nat, S.Nodup → (S.map (ext.get w2).balanceOf).sum ≤ ethBal w2)
    (hinv : ∀ S : List Nat, S.Nodup → (S.map (ext.get w).balanceOf).sum ≤ ethBal w)
    (hok : ((WETH9.withdraw ext wad).run env).run w = .ok ((), w')) :
    ∀ S : List Nat, S.Nodup → (S.map (ext.get w').balanceOf).sum ≤ ethBal w' :=
  S01.WETH9_withdraw ext wad env w w' ethBal hget hbal hrange hcall hinv hok
