import WETH9Bytecode.Conservation

/-!
# WETH9 — S-01, solvency: `Σ balanceOf ≤` the contract's ETH balance

Proved on the Stele spec for every entry point (`weth9_steleExec_solvent`) and carried to the
runtime bytecode through `weth9Correct` (`weth9_bytecode_solvent` and its two corollaries).

**The state `Ξ` starts from already holds `msg.value`** (the value transfer happens in `Θ`, before
the code runs), so "solvent before the call" is `Σ balanceOf + msg.value ≤ balance` on that state.

Per entry point:
* views (`name`, `symbol`, `decimals`, `totalSupply`, `balanceOf`, `allowance`): state unchanged;
* `approve`: one `allowance` write, no balance or ETH change;
* `transfer`, `transferFrom`: `Σ balanceOf` unchanged (`Proofs.WETH9.Conservation`; its
  `Σ < 2^256` premise follows from solvency, since a balance is a 256-bit word);
* `deposit` and the fallback: `balanceOf[msg.sender] += msg.value` raises the sum by at most
  `msg.value` (the solc 0.5 `+` wraps, which only lowers it);
* `withdraw`: `balanceOf[msg.sender] -= wad`, then `msg.sender.call.value(wad)("")`.  The call is
  the EVM's own `Θ` on arbitrary code (`callViaEVM`), which may re-enter WETH9 at any depth.
  Solvency after it is the hypothesis `CallsKeepSolvent self`: every successful message call from
  `self` (holding the WETH9 code) that sends `v` wei while `Σ balanceOf + v ≤ balance` returns
  with `Σ balanceOf ≤ balance`.  It is the induction hypothesis of a proof over the whole EVM
  (call depth ≤ 1024): a nested frame running WETH9's code is covered by this theorem one level
  down, and code at other addresses can neither write WETH9's storage nor take its ETH.  That
  whole-EVM induction is not done here, so the hypothesis is stated, not discharged.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

namespace Benchmarks.WETH9.Props

open Benchmarks.WETH9

/-! ## The invariant -/

/-- Solvency: `Σ balanceOf ≤` the contract's ETH balance. -/
def Solvent (evm : EVM.State) : Prop := totalBal evm ≤ ethBal evm

/-- Solvency *before* the incoming value was credited: the state `Ξ` runs from already holds
    `msg.value`, so "solvent before the call" is `Σ balanceOf + msg.value ≤ balance`. -/
def SolventBefore (evm : EVM.State) : Prop :=
  totalBal evm + evm.executionEnv.weiValue.toNat ≤ ethBal evm

/-- The assumption about the world outside WETH9's own frame (see the module doc): every
    successful message call that the contract at `self` (holding the WETH9 code) makes, sending `v`
    wei while it holds at least `Σ balanceOf + v`, returns with the contract solvent. -/
def CallsKeepSolvent (self : AccountAddress) : Prop :=
  ∀ (σ σ₀ : AccountMap) (A : Substate) (orig r : AccountAddress) (g p v v' : UInt256)
    (d : ByteArray) (e : Fin 1025) (H : BlockHeader) (bvh : List ByteArray)
    (blocks : ProcessedBlocks) (w : Bool) (σ' : AccountMap) (g' : UInt256) (A' : Substate)
    (out : ByteArray),
    HasCode σ self →
    Θ σ σ₀ A self orig r (toExecute σ r) g p v v' d e H bvh blocks w = (σ', g', A', true, out) →
    totalBalAt σ self + v.toNat ≤ ethBalAt σ self →
    totalBalAt σ' self ≤ ethBalAt σ' self

theorem totalBal_le_ethBal_lt {evm : EVM.State} (h : SolventBefore evm) :
    totalBal evm < UInt256.size := by
  have := ethBal_lt evm; unfold SolventBefore at h; omega

/-! ## Views -/

theorem view_block {stele : Frame} {evm evm' : EVM.State} {c : Expr} {es : List Expr}
    {r : ExecResult} (h : ExecBlock config stele evm [.require c, .return es] r)
    (hr : resultState? r = some evm') : evm' = evm := by
  rcases execBlock_require_cons h with rfl | ⟨-, h⟩
  · simp at hr
  rcases execBlock_return_cons h with rfl | ⟨vs, -, rfl⟩
  · simp at hr
  simpa using hr.symm

/-! ## `deposit` and the fallback -/

theorem deposit_block (hinj : SlotsInjective) {L : Store} {I : ExecutionEnv}
    {evm evm' : EVM.State} {r : ExecResult}
    (hL : L.get? "balanceOf" = none) (hsrc : evm.executionEnv = I)
    (h : ExecBlock config { contract := contract, locals := L } evm depositTransition.body r)
    (hr : resultState? r = some evm') :
    evm'.executionEnv = evm.executionEnv ∧ totalBal evm' ≤ totalBal evm + I.weiValue.toNat ∧
      ethBal evm' = ethBal evm := by
  have hco : evm.executionEnv.codeOwner = I.codeOwner := by rw [hsrc]
  have hcv : evm.executionEnv.weiValue = I.weiValue := by rw [hsrc]
  have heval : evalExpr? config { contract := contract, locals := L } evm
      (.binary .add (.storage (balanceOfRef sender)) (.env .callvalue)) =
        .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
          (callerBalSlot I)).toNat + Int.ofNat I.weiValue.toNat)) := by
    have hlhs := evalCallerBal evm I L hsrc hL
    simp only [evalExpr?, hlhs, envValue, hcv, EvalResult.bind, bind, pure, evalBinaryOp?]
    rfl
  have hassign : ∀ n : Int, assignStorageRef? config { contract := contract, locals := L } evm
      .storage (balanceOfRef sender) (.int n) =
      .ok ({ contract := contract, locals := L },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner (callerBalSlot I)
          (EVM.wordOfInt n)) := by
    intro n
    refine Benchmarks.WETH9.assignStorageRef_storage_scalar_value
      (stele := { contract := contract, locals := L }) (slot := balanceOfRef sender)
      (er := callerBalRef I) (ty := uint256St) (loc := wordLoc (callerBalSlot I))
      (hbase := by simpa [balanceOfRef] using hL) (her := ?_) (hty := ?_)
      (hloc := by rfl) (hleaf := by exact Or.inl ⟨_, rfl⟩)
      (hscalar := by trivial) (hstore := ?_)
    · simp only [balanceOfRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        evalExpr?, envValue, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
    · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
    · rw [show wordLoc (callerBalSlot I) = uint256Loc (callerBalSlot I) from rfl,
        storageLocStore_uint256_int]
  simp only [depositTransition] at h
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v, fr', evm₁, hv, ha, h⟩
  · simp at hr
  · simp at hr
  cases heval.symm.trans hv
  cases (hassign _).symm.trans ha
  cases h
  simp only [resultState?_ok, Option.some.injEq] at hr
  subst hr
  rw [wordOfInt_add_words]
  refine ⟨storageStore_executionEnv _ _ _ _, ?_, ethBal_storageStore _ _ _⟩
  by_cases hp : Present evm
  · obtain ⟨acc, hacc⟩ := hp
    unfold totalBal
    rw [show callerBalSlot I = balanceOfSlot (.address I.source) from rfl,
      balOf_storageStore_bal hinj _ _ _ hacc,
      show ∀ a b : UInt256, (UInt256.add a b).toNat = (a.toNat + b.toNat) % UInt256.size
        from fun a b => uadd_toNat a b]
    have hsum := sum_update_add (balOf evm) I.source
      (((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (balanceOfSlot (.address I.source))).toNat + I.weiValue.toNat) % UInt256.size)
    have hmod := Nat.mod_le ((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (balanceOfSlot (.address I.source))).toNat + I.weiValue.toNat) UInt256.size
    change _ + balOf evm I.source = _ at hsum
    have hb : balOf evm I.source = (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (balanceOfSlot (.address I.source))).toNat := rfl
    omega
  · rw [storageStore_missing _ _ _ (not_present evm hp)]
    omega

/-! ## `approve` -/

theorem approve_post (hinj : SlotsInjective) (evm : EVM.State) (I : ExecutionEnv) :
    (approvePostState evm I).executionEnv = evm.executionEnv ∧
      totalBal (approvePostState evm I) = totalBal evm ∧
      ethBal (approvePostState evm I) = ethBal evm := by
  refine ⟨storageStore_executionEnv _ _ _ _, ?_, ethBal_storageStore _ _ _⟩
  unfold totalBal approvePostState
  rw [balOf_storageStore_other evm (approveStorageSlot I) _ (fun a he =>
    hinj.2 I.source (AccountAddress.ofNat (approveGuyWord I).toNat) a (by rw [he]; rfl))]

theorem approve_block (hinj : SlotsInjective) {I : ExecutionEnv} {evm evm' : EVM.State}
    {r : ExecResult} (hsrc : evm.executionEnv.source = I.source)
    (h : ExecBlock config { contract := contract, locals := approveStore I } evm
      approveTransition.body r)
    (hr : resultState? r = some evm') :
    evm'.executionEnv = evm.executionEnv ∧ totalBal evm' = totalBal evm ∧
      ethBal evm' = ethBal evm := by
  simp only [approveTransition, nonpayable, List.cons_append, List.nil_append] at h
  rcases execBlock_require_cons h with rfl | ⟨-, h⟩
  · simp at hr
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v, fr', evm₁, hv, ha, h⟩
  · simp at hr
  · simp at hr
  cases (evalExpr_approve_wad evm I).symm.trans hv
  cases (approveAssign evm I hsrc).symm.trans ha
  rcases execBlock_return_cons h with rfl | ⟨vs, -, rfl⟩
  · simp at hr
  simp only [resultState?_returned, Option.some.injEq] at hr
  subst hr
  exact approve_post hinj evm I

/-! ## `withdraw` -/

theorem balOf_missing (evm : EVM.State) (a : AccountAddress) (hp : ¬ Present evm) :
    balOf evm a = 0 := by
  have hm := not_present evm hp
  simp only [balOf, Stele.EVM.storageLoad, State.lookupAccount, Option.option]
  rw [hm]
  rfl

/-- The debit `balanceOf[msg.sender] -= wad` lowers `Σ balanceOf` by exactly `wad`. -/
theorem withdrawStoreState_total (hinj : SlotsInjective) (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv = I)
    (hle : (withdrawWadWord I).toNat ≤
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat) :
    totalBal (withdrawStoreState evm I) + (withdrawWadWord I).toNat = totalBal evm := by
  have hco : evm.executionEnv.codeOwner = I.codeOwner := by rw [hsrc]
  have hb : balOf evm I.source = (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (callerBalSlot I)).toNat := rfl
  unfold withdrawStoreState
  by_cases hp : Present evm
  · obtain ⟨acc, hacc⟩ := hp
    unfold totalBal
    rw [show callerBalSlot I = balanceOfSlot (.address I.source) from rfl] at hb hle ⊢
    rw [balOf_storageStore_bal hinj _ _ _ hacc, usub_toNat hle]
    have hsum := sum_update_add (balOf evm) I.source
      ((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (balanceOfSlot (.address I.source))).toNat - (withdrawWadWord I).toNat)
    change _ + balOf evm I.source = _ at hsum
    omega
  · rw [storageStore_missing _ _ _ (not_present evm hp)]
    rw [← hb, balOf_missing evm _ hp] at hle
    omega

theorem withdraw_block (hinj : SlotsInjective) {I : ExecutionEnv} {evm evm' : EVM.State}
    {r : ExecResult} (hsrc : evm.executionEnv = I)
    (hcalls : CallsKeepSolvent I.codeOwner) (hcode : HasCode evm.accountMap I.codeOwner)
    (hpre : totalBal evm ≤ ethBal evm)
    (h : ExecBlock config { contract := contract, locals := withdrawStore I } evm
      withdrawTransition.body r)
    (hr : resultState? r = some evm') :
    evm'.executionEnv = evm.executionEnv ∧ Solvent evm' := by
  have hco : evm.executionEnv.codeOwner = I.codeOwner := by rw [hsrc]
  simp only [withdrawTransition, nonpayable, List.cons_append, List.nil_append] at h
  rcases execBlock_require_cons h with rfl | ⟨-, h⟩
  · simp at hr
  rcases execBlock_require_cons h with rfl | ⟨hc, h⟩
  · simp at hr
  by_cases hle : (withdrawWadWord I).toNat ≤
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat
  swap
  · cases (evalWithdrawGe_false evm I hsrc (by omega)).symm.trans hc
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v, fr', evm₂, hv, ha, h⟩
  · simp at hr
  · simp at hr
  cases (evalWithdrawSub evm I hsrc).symm.trans hv
  cases (withdrawAssign evm I hsrc hle).symm.trans ha
  have henv₂ : (withdrawStoreState evm I).executionEnv = I := by
    rw [withdrawStoreState, storageStore_executionEnv, hsrc]
  cases h with
  | consNormal hst hrest =>
    cases hst with
    | lowLevelCallSuccess hperm hrecv heth hcd hcall =>
      cases (evalWithdrawSender _ _).symm.trans hrecv
      cases (evalWithdrawWadVar _ I).symm.trans heth
      cases (evalWithdrawEmptyBytes _ _).symm.trans hcd
      rcases execBlock_require_cons hrest with rfl | ⟨-, hrest⟩
      · simp at hr
      cases hrest
      simp only [resultState?_ok, Option.some.injEq] at hr
      subst hr
      cases hcall with
      | callMade hvw hΘ hev _ _ =>
        obtain ⟨callGas, A_in, hΘ⟩ := hΘ
        subst hev hvw
        rw [henv₂] at hΘ
        refine ⟨by simp [henv₂, hsrc], ?_⟩
        unfold Solvent ethBal
        rw [totalBal_eq_At]
        simp only [henv₂]
        refine hcalls _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ hΘ.symm ?_
        · rw [withdrawStoreState, ← hco]
          exact hasCode_storageStore evm _ _ (hco ▸ hcode)
        · rw [wordOfInt_ofNat_toNat]
          have htot := withdrawStoreState_total hinj evm I hsrc hle
          have heth : ethBal (withdrawStoreState evm I) = ethBal evm := by
            rw [withdrawStoreState]; exact ethBal_storageStore _ _ _
          rw [totalBal_eq_At, henv₂] at htot
          unfold ethBal at heth hpre
          rw [henv₂] at heth
          rw [heth]
          omega
    | lowLevelCallFailure hperm hrecv heth hcd hcall =>
      rcases execBlock_require_cons hrest with rfl | ⟨hc', -⟩
      · simp at hr
      cases (evalWithdrawSuccess _ I false _).symm.trans hc'
  | consRevert _ => simp at hr
  | consStatic _ => simp at hr
  | consReturn hst => cases hst
  | consBreak hst => cases hst
  | consContinue hst => cases hst

/-! ## The dispatcher -/

theorem weth9Decode_deposit_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (depositTransition.params.map Param.name)
      (transitionSignature depositTransition).paramTypes I.calldata = some ∅ := by
  change decodeCalldataWithMode .modern [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

theorem view_returned {t : TransitionDecl} {c : Expr} {es : List Expr}
    (ht : t.body = [.require c, .return es]) {evm evm' : EVM.State} {L : Store} {fr' : Frame}
    {ret : Option (List Value)}
    (h : ExecTransitionBody config contract evm L t.body (.returned fr' evm' ret)) :
    evm' = evm := by
  obtain ⟨r, hb, hr⟩ := execFuncBody_block h
  rw [ht] at hb
  exact view_block hb (hr.trans (resultState?_returned _ _ _))

/-- **S-01 on the spec.**  Whatever the WETH9 spec returns for any call — every selector, the
    fallback, any caller, value and calldata — the returned state is solvent if the initial one was
    solvent before the call's value was credited.  A `withdraw` call additionally needs the
    outgoing ETH send to keep solvency (`CallsKeepSolvent`) and the contract to hold the WETH9
    code. -/
theorem weth9_steleExec_solvent (hinj : SlotsInjective)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} {rc : ReturnConvention}
    {fr' : Frame} {evm' : EVM.State} {ret : Option (List Value)}
    (hwd : selIs I (weth9SelBytes 4) → CallsKeepSolvent I.codeOwner ∧ HasCode σ I.codeOwner)
    (hpre : SolventBefore (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hexec : steleExec config contract ∅ σ σ₀ g A I (.returned fr' evm' ret) rc) :
    evm'.executionEnv = I ∧ Solvent evm' := by
  have hsrc : (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv = I := rfl
  have hsol : totalBal (initState σ σ₀ (Sat256.ofUInt256 g) A I) ≤
      ethBal (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by unfold SolventBefore at hpre; omega
  have hlt : totalBal (initState σ σ₀ (Sat256.ofUInt256 g) A I) < UInt256.size :=
    totalBal_le_ethBal_lt hpre
  cases hexec with
  | intro hs hsig hdec hst hbody =>
    subst hsig hst
    have hsz4 : 4 ≤ I.calldata.size := by
      by_contra hshort
      rw [weth9SelDispatch_none_short (by omega)] at hs
      cases hs
    have hs' := hs
    rw [selectorDispatchMsg_eq_dispatchList] at hs'
    have hmem := dispatchList_some_mem hs'
    simp only [contract, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- name
      obtain rfl := view_returned rfl hbody; exact ⟨rfl, hsol⟩
    · -- approve
      by_cases h68 : 68 ≤ I.calldata.size
      · cases (weth9Decode_approve_ok h68).symm.trans hdec
        obtain ⟨r, hb, hr⟩ := execFuncBody_block hbody
        have hb2 : ExecBlock config { contract := contract, locals := approveStore I }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) approveTransition.body r := hb
        have hr2 : resultState? r = some evm' := hr.trans (resultState?_returned _ _ _)
        obtain ⟨he, ht, hb'⟩ := approve_block hinj (I := I) (hsrc := rfl) hb2 hr2
        refine ⟨he, ?_⟩
        unfold Solvent; rw [ht, hb']; exact hsol
      · cases (weth9Decode_approve_none_short hsz4 (by omega)).symm.trans hdec
    · -- totalSupply
      obtain rfl := view_returned rfl hbody; exact ⟨rfl, hsol⟩
    · -- transferFrom
      by_cases h100 : 100 ≤ I.calldata.size
      · cases (tfDecode_ok h100).symm.trans hdec
        have hb2 : ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (tfStore I)
          transferFromTransition.body (.returned fr' evm' ret) := hbody
        obtain ⟨he, ht, hb'⟩ := transferFrom_returned_conserves hinj hlt hb2
        refine ⟨he, ?_⟩
        unfold Solvent; rw [ht, hb']; exact hsol
      · cases (tfDecode_none_short hsz4 (by omega)).symm.trans hdec
    · -- withdraw
      have hsel := dispatchList_some_selIs hs'
      rw [selectorOf, weth9WithdrawSelectorBytes] at hsel
      obtain ⟨hcalls, hcode⟩ := hwd hsel
      by_cases h36 : 36 ≤ I.calldata.size
      · cases (weth9Decode_withdraw_ok h36).symm.trans hdec
        obtain ⟨r, hb, hr⟩ := execFuncBody_block hbody
        have hb2 : ExecBlock config { contract := contract, locals := withdrawStore I }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) withdrawTransition.body r := hb
        have hr2 : resultState? r = some evm' := hr.trans (resultState?_returned _ _ _)
        exact withdraw_block hinj hsrc hcalls hcode hsol hb2 hr2
      · cases (weth9Decode_withdraw_none_short hsz4 (by omega)).symm.trans hdec
    · -- decimals
      obtain rfl := view_returned rfl hbody; exact ⟨rfl, hsol⟩
    · -- balanceOf
      obtain rfl := view_returned rfl hbody; exact ⟨rfl, hsol⟩
    · -- symbol
      obtain rfl := view_returned rfl hbody; exact ⟨rfl, hsol⟩
    · -- transfer
      by_cases h68 : 68 ≤ I.calldata.size
      · cases (xferDecode_ok h68).symm.trans hdec
        have hb2 : ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (transferStore I)
          transferTransition.body (.returned fr' evm' ret) := hbody
        obtain ⟨he, ht, hb'⟩ := transfer_returned_conserves hinj rfl hlt hb2
        refine ⟨he, ?_⟩
        unfold Solvent; rw [ht, hb']; exact hsol
      · cases (xferDecode_none_short hsz4 (by omega)).symm.trans hdec
    · -- deposit
      cases (weth9Decode_deposit_ok hsz4).symm.trans hdec
      obtain ⟨r, hb, hr⟩ := execFuncBody_block hbody
      have hb2 : ExecBlock config { contract := contract, locals := ∅ }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) depositTransition.body r := hb
      have hr2 : resultState? r = some evm' := hr.trans (resultState?_returned _ _ _)
      obtain ⟨he, ht, hb'⟩ := deposit_block hinj (by simp) hsrc hb2 hr2
      refine ⟨he, ?_⟩
      have hwv : (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.weiValue = I.weiValue := rfl
      unfold Solvent SolventBefore at *; rw [hb']; rw [hwv] at hpre; omega
    · -- allowance
      obtain rfl := view_returned rfl hbody; exact ⟨rfl, hsol⟩
  | fallback hs hrecv hfb hargs hrc hst hbody =>
    subst hst
    rw [show contract.fallback = some fallbackTransition from rfl] at hfb
    cases hfb
    cases hargs
    obtain ⟨r, hb, hr⟩ := execFuncBody_block hbody
    have hb2 : ExecBlock config { contract := contract, locals := ∅ }
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) depositTransition.body r := hb
    have hr2 : resultState? r = some evm' := hr.trans (resultState?_returned _ _ _)
    obtain ⟨he, ht, hb'⟩ := deposit_block hinj (by simp) hsrc hb2 hr2
    refine ⟨he, ?_⟩
    have hwv : (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.weiValue = I.weiValue := rfl
    unfold Solvent SolventBefore at *; rw [hb']; rw [hwv] at hpre; omega
  | receive hr =>
    rw [weth9_receive_none] at hr; cases hr

/-! ## The bytecode -/

/-- **S-01 on the bytecode.**  If the EVM runs the WETH9 runtime bytecode — any accounts, gas,
    substate, caller, value and calldata, every selector and the fallback — and the call succeeds,
    then the contract is solvent afterwards (`Σ balanceOf ≤` its ETH balance) whenever it was
    solvent before the call's value was credited (`Σ balanceOf + msg.value ≤` the balance `Ξ`
    starts from).  Hypotheses: `SlotsInjective` (Keccak), `weth9StorageWF` (the refinement's own
    precondition: a stored `name`/`symbol` string shorter than `2^64` bytes), and, for a `withdraw`
    call only, `CallsKeepSolvent` for the contract's address and the WETH9 code at that address. -/
theorem weth9_bytecode_solvent (hinj : SlotsInjective)
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate} {I : ExecutionEnv} {o : ByteArray}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : weth9StorageWF σ I)
    (hwd : selIs I (weth9SelBytes 4) → CallsKeepSolvent I.codeOwner ∧ HasCode σ I.codeOwner)
    (hpre : totalBalAt σ I.codeOwner + I.weiValue.toNat ≤ ethBalAt σ I.codeOwner)
    (hΞ : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    totalBalAt σ' I.codeOwner ≤ ethBalAt σ' I.codeOwner := by
  obtain ⟨hrun⟩ := weth9Correct
  cases hrun σ σ₀ g A I hcode hsize hwf trivial with
  | execution hΞ' hstele hequiv =>
    obtain rfl := hΞ'.symm.trans hΞ
    cases hequiv with
    | success h1 h2 h3 _ =>
      cases h1
      subst h2 h3
      obtain ⟨henv, hsol⟩ := weth9_steleExec_solvent hinj hwd hpre hstele
      unfold Solvent ethBal at hsol
      rw [totalBal_eq_At, henv] at hsol
      exact hsol
    | revert h1 _ => cases h1
    | noMatch h1 _ => cases h1
    | decodingFailed h1 _ => cases h1
    | invalidHalt h1 _ => cases h1
    | staticHalt h1 _ => cases h1
  | outOfGas hΞ' => cases hΞ'.symm.trans hΞ

/-- S-01 for every call that is not `withdraw` — `deposit`, the fallback, `approve`, `transfer`,
    `transferFrom` and the views — with no assumption about other contracts. -/
theorem weth9_bytecode_solvent_of_not_withdraw (hinj : SlotsInjective)
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate} {I : ExecutionEnv} {o : ByteArray}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : weth9StorageWF σ I) (hnw : ¬ selIs I (weth9SelBytes 4))
    (hpre : totalBalAt σ I.codeOwner + I.weiValue.toNat ≤ ethBalAt σ I.codeOwner)
    (hΞ : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    totalBalAt σ' I.codeOwner ≤ ethBalAt σ' I.codeOwner :=
  weth9_bytecode_solvent hinj hcode hsize hwf (fun h => absurd h hnw) hpre hΞ

/-- S-01 for every call, `withdraw` included, given `CallsKeepSolvent` and the WETH9 code at the
    contract's address. -/
theorem weth9_bytecode_solvent_all (hinj : SlotsInjective)
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate} {I : ExecutionEnv} {o : ByteArray}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : weth9StorageWF σ I)
    (hcalls : CallsKeepSolvent I.codeOwner) (hself : HasCode σ I.codeOwner)
    (hpre : totalBalAt σ I.codeOwner + I.weiValue.toNat ≤ ethBalAt σ I.codeOwner)
    (hΞ : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    totalBalAt σ' I.codeOwner ≤ ethBalAt σ' I.codeOwner :=
  weth9_bytecode_solvent hinj hcode hsize hwf (fun _ => ⟨hcalls, hself⟩) hpre hΞ

end Benchmarks.WETH9.Props
