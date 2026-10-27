import WETH9Bytecode.Balances

/-!
# WETH9 — S-03, conservation: `transfer` and `transferFrom` keep `Σ balanceOf`

The property is proved on the Stele spec of `Benchmarks.WETH9` and carried down to the runtime
bytecode through the refinement theorem `weth9Correct`, as `Proofs.ERC20.Bytecode` does for the
ERC20 supply invariant:

* `tf_block_conserves`: the `transferFrom` body, run on any locals binding `src`, `dst`, `wad`,
  either reverts/halts or returns a state with the same `Σ balanceOf` (`src = dst` included);
* `transferFrom_returned_conserves`, `transfer_returned_conserves`: the two transitions (`transfer`
  is the internal call `transferFrom(msg.sender, dst, wad)`);
* `weth9_steleExec_conserves`: any `steleExec` run that selects either one;
* `weth9_bytecode_conserves`: any successful `Ξ` run of `weth9Bytecode` with either selector.

Hypotheses, both explicit:
* `SlotsInjective` — Keccak collision-freedom for the `balanceOf`/`allowance` slots;
* `Σ balanceOf < 2^256` before the call — WETH9 is solc 0.5 code, `balanceOf[dst] += wad` wraps
  modulo `2^256`, so with a pre-sum at or above `2^256` the credited balance can wrap and the sum
  drop.  Any state where S-01 (solvency) holds satisfies it, since the contract's ETH balance is a
  256-bit word.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

namespace Benchmarks.WETH9.Props

open Benchmarks.WETH9

/-- The locals a `transferFrom` body runs with: `src`, `dst`, `wad` bound, no storage names
    shadowed. -/
structure TFArgs (S : Store) (s d : AccountAddress) (w : UInt256) : Prop where
  src : S.get? "src" = some (.address s)
  dst : S.get? "dst" = some (.address d)
  wad : S.get? "wad" = some (.int (Int.ofNat w.toNat))
  bal : S.get? "balanceOf" = none
  allow : S.get? "allowance" = none

section Eval

variable {S : Store} {s d : AccountAddress} {w : UInt256} (evm : EVM.State)

abbrev fr (S : Store) : Frame := { contract := contract, locals := S }

theorem ev_bal_var (hS : TFArgs S s d w) (x : String) (y : AccountAddress) (hx : S.get? x = some (.address y)) :
    evalExpr? config (fr S) evm (.storage (balanceOfRef (.var x))) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (balanceOfSlot (.address y))).toNat)) := by
  refine evalExpr_storage_scalar_value
    (stele := fr S) (slot := balanceOfRef (.var x))
    (er := { base := "balanceOf", steps := [.mindex (.address y)] })
    (t := .int uint256Int) (loc := wordLoc (balanceOfSlot (.address y)))
    (hbase := hS.bal) ?_ ?_ (by rfl) ?_
  · have hx' : S[x]? = some (.address y) := by rw [← Std.HashMap.get?_eq_getElem?]; exact hx
    simp [evalStorageRef, evalStorageRefStep, balanceOfRef, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hx']
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · rw [show wordLoc (balanceOfSlot (.address y)) = uint256Loc (balanceOfSlot (.address y))
      from rfl, storageLocLoad_uint256]

theorem ev_wad (hS : TFArgs S s d w) : evalExpr? config (fr S) evm (.var "wad") = .ok (.int (Int.ofNat w.toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]; rw [hS.wad]

theorem ev_allow (hS : TFArgs S s d w) :
    evalExpr? config (fr S) evm (.storage (allowanceRef (.var "src") sender)) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (allowanceSlot (.address s) (.address evm.executionEnv.source))).toNat)) := by
  refine evalExpr_storage_scalar_value
    (stele := fr S) (slot := allowanceRef (.var "src") sender)
    (er := { base := "allowance",
             steps := [.mindex (.address s), .mindex (.address evm.executionEnv.source)] })
    (t := .int uint256Int)
    (loc := wordLoc (allowanceSlot (.address s) (.address evm.executionEnv.source)))
    (hbase := hS.allow) ?_ ?_ (by rfl) ?_
  · simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
      show S[("src" : String)]? = some (.address s) by rw [← Std.HashMap.get?_eq_getElem?]; exact hS.src]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · rw [show wordLoc (allowanceSlot (.address s) (.address evm.executionEnv.source))
        = uint256Loc (allowanceSlot (.address s) (.address evm.executionEnv.source)) from rfl,
      storageLocLoad_uint256]


theorem ge_true_le (hS : TFArgs S s d w)
    (h : evalExpr? config (fr S) evm
      (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")) = .ok (.bool true)) :
    w.toNat ≤ (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (balanceOfSlot (.address s))).toNat := by
  unfold evalExpr? at h
  rw [ev_bal_var evm hS "src" s hS.src, ev_wad evm hS] at h
  simp [EvalResult.bind, bind, evalBinaryOp?] at h
  omega

theorem ev_sub_src (hS : TFArgs S s d w) :
    evalExpr? config (fr S) evm
      (.binary .sub (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (balanceOfSlot (.address s))).toNat - Int.ofNat w.toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [ev_bal_var evm hS "src" s hS.src, ev_wad evm hS]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem ev_add_dst (hS : TFArgs S s d w) :
    evalExpr? config (fr S) evm
      (.binary .add (.storage (balanceOfRef (.var "dst"))) (.var "wad")) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (balanceOfSlot (.address d))).toNat + Int.ofNat w.toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [ev_bal_var evm hS "dst" d hS.dst, ev_wad evm hS]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem ev_allow_sub (hS : TFArgs S s d w) :
    evalExpr? config (fr S) evm
      (.binary .sub (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (allowanceSlot (.address s) (.address evm.executionEnv.source))).toNat
          - Int.ofNat w.toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [ev_allow evm hS, ev_wad evm hS]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem as_bal_var (hS : TFArgs S s d w) (x : String) (y : AccountAddress)
    (hx : S.get? x = some (.address y)) (n : Int) :
    assignStorageRef? config (fr S) evm .storage (balanceOfRef (.var x)) (.int n) =
      .ok (fr S, Stele.EVM.storageStore evm evm.executionEnv.codeOwner
        (balanceOfSlot (.address y)) (EVM.wordOfInt n)) := by
  refine assignStorageRef_storage_scalar_value (hleaf := by simp [uint256St])
    (er := { base := "balanceOf", steps := [.mindex (.address y)] })
    (ty := uint256St) (loc := wordLoc (balanceOfSlot (.address y)))
    (hbase := hS.bal) ?_ ?_ (by rfl) (by trivial) ?_
  · have hx' : S[x]? = some (.address y) := by rw [← Std.HashMap.get?_eq_getElem?]; exact hx
    simp [evalStorageRef, evalStorageRefStep, balanceOfRef, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hx']
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · rw [show wordLoc (balanceOfSlot (.address y)) = uint256Loc (balanceOfSlot (.address y))
      from rfl, storageLocStore_uint256_int]

theorem as_allow (hS : TFArgs S s d w) (n : Int) :
    assignStorageRef? config (fr S) evm .storage (allowanceRef (.var "src") sender) (.int n) =
      .ok (fr S, Stele.EVM.storageStore evm evm.executionEnv.codeOwner
        (allowanceSlot (.address s) (.address evm.executionEnv.source)) (EVM.wordOfInt n)) := by
  refine assignStorageRef_storage_scalar_value (hleaf := by simp [uint256St])
    (er := { base := "allowance",
             steps := [.mindex (.address s), .mindex (.address evm.executionEnv.source)] })
    (ty := uint256St)
    (loc := wordLoc (allowanceSlot (.address s) (.address evm.executionEnv.source)))
    (hbase := hS.allow) ?_ ?_ (by rfl) (by trivial) ?_
  · simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
      show S[("src" : String)]? = some (.address s) by rw [← Std.HashMap.get?_eq_getElem?]; exact hS.src]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · rw [show wordLoc (allowanceSlot (.address s) (.address evm.executionEnv.source))
        = uint256Loc (allowanceSlot (.address s) (.address evm.executionEnv.source)) from rfl,
      storageLocStore_uint256_int]

end Eval

/-! ## The `transferFrom` body -/

/-- The allowance branch `if (src != msg.sender && allowance != max) { require; allowance -= wad }`
    either reverts, halts in static mode, or falls through with the same frame, having written at
    most an `allowance` slot. -/
theorem tf_ite_result {S : Store} {s d : AccountAddress} {w : UInt256} (hS : TFArgs S s d w)
    {evm : EVM.State} {c : Expr} {r : ExecResult}
    (h : ExecStmt config (fr S) evm
      (.ite c
        [ .require (.binary .ge (.storage (allowanceRef (.var "src") sender)) (.var "wad")),
          .assign .storage (allowanceRef (.var "src") sender)
            (.binary .sub (.storage (allowanceRef (.var "src") sender)) (.var "wad")) ]
        []) r) :
    r = .reverted ∨ r = .staticViolation ∨ r = .ok (fr S) evm ∨
      ∃ v, r = .ok (fr S) (Stele.EVM.storageStore evm evm.executionEnv.codeOwner
        (allowanceSlot (.address s) (.address evm.executionEnv.source)) v) := by
  cases h with
  | iteTrue _ hb =>
    rcases execBlock_require_cons hb with rfl | ⟨-, hb⟩
    · exact Or.inl rfl
    rcases execBlock_assign_cons hb with rfl | rfl | ⟨v, fr', evm', hv, ha, hb⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    cases (ev_allow_sub evm hS).symm.trans hv
    cases (as_allow evm hS _).symm.trans ha
    cases hb
    exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
  | iteFalse _ hb =>
    cases hb
    exact Or.inr (Or.inr (Or.inl rfl))
  | iteCondRevert _ => exact Or.inl rfl

/-- **The `transferFrom` body conserves `Σ balanceOf`.**  Whatever state a run of the body
    reaches, it has the same environment and the same sum of balances — provided the sum starts
    below `2^256` (the add to `balanceOf[dst]` is solc 0.5's wrapping `+`). -/
theorem tf_block_conserves (hinj : SlotsInjective) {S : Store} {s d : AccountAddress}
    {w : UInt256} (hS : TFArgs S s d w) {evm evm' : EVM.State} {r : ExecResult}
    (hlt : totalBal evm < UInt256.size)
    (h : ExecBlock config (fr S) evm transferFromTransition.body r)
    (hr : resultState? r = some evm') :
    evm'.executionEnv = evm.executionEnv ∧ totalBal evm' = totalBal evm ∧
      ethBal evm' = ethBal evm := by
  simp only [transferFromTransition, nonpayable, List.cons_append, List.nil_append] at h
  -- require(msg.value == 0)
  rcases execBlock_require_cons h with rfl | ⟨-, h⟩
  · simp at hr
  -- require(balanceOf[src] >= wad)
  rcases execBlock_require_cons h with rfl | ⟨hc, h⟩
  · simp at hr
  have henough := ge_true_le evm hS hc
  -- the allowance branch
  obtain ⟨evm₁, hco₁, hbal₁, heth₁, h⟩ : ∃ evm₁ : EVM.State, evm₁.executionEnv = evm.executionEnv ∧
      balOf evm₁ = balOf evm ∧ ethBal evm₁ = ethBal evm ∧
      ExecBlock config (fr S) evm₁
        [ .assign .storage (balanceOfRef (.var "src"))
            (.binary .sub (.storage (balanceOfRef (.var "src"))) (.var "wad")),
          .assign .storage (balanceOfRef (.var "dst"))
            (.binary .add (.storage (balanceOfRef (.var "dst"))) (.var "wad")),
          .return [.boolLit true] ] r := by
    cases h with
    | consNormal hst hrest =>
      rcases tf_ite_result hS hst with h | h | h | ⟨v, h⟩
      · cases h
      · cases h
      · cases h; exact ⟨evm, rfl, rfl, rfl, hrest⟩
      · cases h
        refine ⟨_, storageStore_executionEnv _ _ _ _, ?_, ethBal_storageStore _ _ _, hrest⟩
        exact balOf_storageStore_other _ _ _ (fun a he => hinj.2 _ _ a he.symm)
    | consReturn hst => rcases tf_ite_result hS hst with h | h | h | ⟨v, h⟩ <;> cases h
    | consRevert _ => simp at hr
    | consBreak hst => rcases tf_ite_result hS hst with h | h | h | ⟨v, h⟩ <;> cases h
    | consContinue hst => rcases tf_ite_result hS hst with h | h | h | ⟨v, h⟩ <;> cases h
    | consStatic _ => simp at hr
  -- balanceOf[src] = balanceOf[src] - wad
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₂, fr₂, evm₂, hv₂, ha₂, h⟩
  · simp at hr
  · simp at hr
  cases (ev_sub_src evm₁ hS).symm.trans hv₂
  cases (as_bal_var evm₁ hS "src" s hS.src _).symm.trans ha₂
  -- balanceOf[dst] = balanceOf[dst] + wad
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₃, fr₃, evm₃, hv₃, ha₃, h⟩
  · simp at hr
  · simp at hr
  cases (ev_add_dst _ hS).symm.trans hv₃
  cases (as_bal_var _ hS "dst" d hS.dst _).symm.trans ha₃
  -- return true
  rcases execBlock_return_cons h with rfl | ⟨vs, -, rfl⟩
  · simp at hr
  simp only [resultState?_returned, Option.some.injEq] at hr
  subst hr
  rw [wordOfInt_sub_natCasts, wordOfInt_add_words]
  set f := balOf evm₁ with hf
  set e₂ := Stele.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner (balanceOfSlot (.address s))
    (UInt256.sub (Stele.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner
      (balanceOfSlot (.address s))) w) with he₂
  have hco₂ : e₂.executionEnv = evm₁.executionEnv := storageStore_executionEnv _ _ _ _
  refine ⟨by rw [storageStore_executionEnv, hco₂, hco₁], ?_,
    by rw [ethBal_storageStore, he₂, ethBal_storageStore, heth₁]⟩
  have henough' : w.toNat ≤ f s := by rw [hbal₁]; exact henough
  unfold totalBal
  rw [← hbal₁]
  by_cases hp : Present evm₁
  · obtain ⟨acc, hacc⟩ := hp
    have hb₂ : balOf e₂ = Function.update f s (f s - w.toNat) := by
      rw [he₂, balOf_storageStore_bal hinj _ _ _ hacc, usub_toNat henough']; rfl
    obtain ⟨acc₂, hacc₂⟩ := storageStore_present evm₁ (balanceOfSlot (.address s))
      (UInt256.sub (Stele.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner
        (balanceOfSlot (.address s))) w) hacc
    rw [← he₂] at hacc₂
    rw [show e₂.executionEnv.codeOwner = e₂.executionEnv.codeOwner from rfl,
      balOf_storageStore_bal hinj _ _ _ hacc₂,
      show ∀ a b : UInt256, (UInt256.add a b).toNat = (a.toNat + b.toNat) % UInt256.size
        from fun a b => uadd_toNat a b]
    change (∑ a, Function.update (balOf e₂) d ((balOf e₂ d + w.toNat) % UInt256.size) a) = _
    rw [hb₂]
    by_cases hsd : s = d
    · subst hsd
      rw [Function.update_self, Nat.sub_add_cancel henough',
        Nat.mod_eq_of_lt (balOf_lt evm₁ s), Function.update_idem, Function.update_eq_self]
    · rw [Function.update_of_ne (Ne.symm hsd)]
      have hle := add_le_sum f hsd
      have hlt' : (∑ a, f a) < UInt256.size := by
        rw [hbal₁]; exact hlt
      rw [Nat.mod_eq_of_lt (by omega)]
      exact sum_transfer_eq f hsd _ henough'
  · have hm₁ := not_present evm₁ hp
    have hm₂ : e₂ = evm₁ := storageStore_missing _ _ _ hm₁
    rw [hm₂, storageStore_missing _ _ _ hm₁]

/-! ## `transferFrom` and `transfer` as transitions -/

theorem tfStore_args (I : ExecutionEnv) :
    TFArgs (tfStore I) (AccountAddress.ofNat (tfSrcWord I).toNat)
      (AccountAddress.ofNat (tfDstWord I).toNat) (tfWadWord I) where
  src := tfStore_get_src I
  dst := by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_getElem (by simp [tfStore]),
      tfStore_index_dst]
  wad := tfStore_get_wad I
  bal := tfStore_get_balanceOf I
  allow := tfStore_get_allowance I

theorem transferCallStore_args (I : ExecutionEnv) :
    TFArgs (transferCallStore I) I.source (AccountAddress.ofNat (xferDstWord I).toNat)
      (xferWadWord I) where
  src := transferCallStore_get_src I
  dst := transferCallStore_get_dst I
  wad := transferCallStore_get_wad I
  bal := by simp [transferCallStore]
  allow := by simp [transferCallStore]

/-- `transferFrom`: every run that returns conserves `Σ balanceOf`. -/
theorem transferFrom_returned_conserves (hinj : SlotsInjective) {I : ExecutionEnv}
    {evm evm' : EVM.State} {fr' : Frame} {ret : Option (List Value)}
    (hlt : totalBal evm < UInt256.size)
    (h : ExecTransitionBody config contract evm (tfStore I) transferFromTransition.body
      (.returned fr' evm' ret)) :
    evm'.executionEnv = evm.executionEnv ∧ totalBal evm' = totalBal evm ∧
      ethBal evm' = ethBal evm := by
  obtain ⟨r, hb, hr⟩ := execFuncBody_block h
  exact tf_block_conserves hinj (tfStore_args I) hlt hb (hr.trans (resultState?_returned _ _ _))

/-- `transfer` (the internal call `transferFrom(msg.sender, dst, wad)`): every run that returns
    conserves `Σ balanceOf`. -/
theorem transfer_returned_conserves (hinj : SlotsInjective) {I : ExecutionEnv}
    {evm evm' : EVM.State} {fr' : Frame} {ret : Option (List Value)}
    (hsrc : evm.executionEnv.source = I.source)
    (hlt : totalBal evm < UInt256.size)
    (h : ExecTransitionBody config contract evm (transferStore I) transferTransition.body
      (.returned fr' evm' ret)) :
    evm'.executionEnv = evm.executionEnv ∧ totalBal evm' = totalBal evm ∧
      ethBal evm' = ethBal evm := by
  obtain ⟨r, hb, hr⟩ := execFuncBody_block h
  have hr' : resultState? r = some evm' := hr.trans (resultState?_returned _ _ _)
  simp only [transferTransition, nonpayable, List.cons_append, List.nil_append] at hb
  rcases execBlock_require_cons hb with rfl | ⟨-, hb⟩
  · simp at hr'
  cases hb with
  | consNormal hst hrest =>
    cases hst with
    | internalCallReturn hargs hlook hbind hbody =>
      cases (xferEvalArgs evm I hsrc).symm.trans hargs
      have hl : lookupCallable? contract "transferFrom" =
          some transferFromTransition.toCallable := rfl
      cases hl.symm.trans hlook
      cases (transferCallStore_bind I).symm.trans hbind
      obtain ⟨r', hb', hr''⟩ := execFuncBody_block hbody
      have key := tf_block_conserves hinj (transferCallStore_args I) hlt hb'
        (hr''.trans (resultState?_returned _ _ _))
      rcases execBlock_return_cons hrest with rfl | ⟨vs, -, rfl⟩
      · simp at hr'
      simp only [resultState?_returned, Option.some.injEq] at hr'
      subst hr'
      exact key
  | consRevert _ => simp at hr'
  | consStatic _ => simp at hr'
  | consReturn hst => cases hst
  | consBreak hst => cases hst
  | consContinue hst => cases hst

/-! ## The dispatcher -/

/-- `Σ balanceOf` of an account map, in the storage of `owner`. -/
noncomputable def totalBalAt (σ : AccountMap) (owner : AccountAddress) : ℕ :=
  totalBal { (default : EVM.State) with accountMap := σ, executionEnv.codeOwner := owner }

theorem totalBal_eq_At (evm : EVM.State) :
    totalBal evm = totalBalAt evm.accountMap evm.executionEnv.codeOwner := rfl

/-- **S-03 on the spec.**  Whatever the WETH9 spec returns for a call that selects `transfer` or
    `transferFrom`, the returned state belongs to the same call and has the same `Σ balanceOf`,
    provided the sum starts below `2^256`. -/
theorem weth9_steleExec_conserves (hinj : SlotsInjective)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} {rc : ReturnConvention}
    {fr' : Frame} {evm' : EVM.State} {ret : Option (List Value)}
    (hsel : selIs I (weth9SelBytes 8) ∨ selIs I (weth9SelBytes 3))
    (hlt : totalBal (initState σ σ₀ (Sat256.ofUInt256 g) A I) < UInt256.size)
    (hexec : steleExec config contract ∅ σ σ₀ g A I (.returned fr' evm' ret) rc) :
    evm'.executionEnv = I ∧
      totalBal evm' = totalBal (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hdisp : selectorDispatchMsg contract I.calldata = some transferTransition ∨
      selectorDispatchMsg contract I.calldata = some transferFromTransition :=
    hsel.imp weth9SelectorDispatchTransfer weth9SelectorDispatchTransferFrom
  have hsz4 : 4 ≤ I.calldata.size := by
    rcases hsel with h | h
    · exact calldata_size_ge_of_selIs I (weth9SelBytes 8) (by native_decide) h
    · exact calldata_size_ge_of_selIs I (weth9SelBytes 3) (by native_decide) h
  cases hexec with
  | intro hs hsig hdec hst hbody =>
    subst hsig hst
    rcases hdisp with hd | hd
    · cases hs.symm.trans hd
      by_cases h68 : 68 ≤ I.calldata.size
      · cases (xferDecode_ok h68).symm.trans hdec
        have h := transfer_returned_conserves hinj rfl hlt hbody
        exact ⟨h.1, h.2.1⟩
      · cases (xferDecode_none_short hsz4 (by omega)).symm.trans hdec
    · cases hs.symm.trans hd
      by_cases h100 : 100 ≤ I.calldata.size
      · cases (tfDecode_ok h100).symm.trans hdec
        have h := transferFrom_returned_conserves hinj hlt hbody
        exact ⟨h.1, h.2.1⟩
      · cases (tfDecode_none_short hsz4 (by omega)).symm.trans hdec
  | fallback hs =>
    rcases hdisp with hd | hd <;> cases hs.symm.trans hd
  | receive hr =>
    rw [weth9_receive_none] at hr; cases hr

/-! ## The bytecode -/

theorem not_selIs_of_selIs {I : ExecutionEnv} {i j : ℕ} (hi : selIs I (weth9SelBytes i))
    (hne : (weth9SelBytes j == weth9SelBytes i) = false) : ¬ selIs I (weth9SelBytes j) := by
  intro hj
  have he := byteArray_eq_of_beq hi
  unfold selIs at hj
  rw [← he, hne] at hj
  cases hj

/-- The refinement's storage precondition only constrains `name()` and `symbol()` calls. -/
theorem weth9StorageWF_of_sel {σ : AccountMap} {I : ExecutionEnv}
    (hn : ¬ selIs I (weth9SelBytes 0)) (hs : ¬ selIs I (weth9SelBytes 7)) :
    weth9StorageWF σ I :=
  ⟨fun h => absurd h hn, fun h => absurd h hs⟩

/-- **S-03 on the bytecode: `transfer` and `transferFrom` conserve `Σ balanceOf`.**  If the EVM
    runs the WETH9 runtime bytecode on a call whose selector is `transfer` or `transferFrom` — any
    accounts, gas, substate, caller, value and calldata — and the call succeeds, the sum of
    `balanceOf` over all addresses in the returned account map equals the one in the initial
    account map (including `src = dst`), provided it started below `2^256`. -/
theorem weth9_bytecode_conserves (hinj : SlotsInjective)
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate} {I : ExecutionEnv} {o : ByteArray}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 8) ∨ selIs I (weth9SelBytes 3))
    (hlt : totalBalAt σ I.codeOwner < UInt256.size)
    (hΞ : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    totalBalAt σ' I.codeOwner = totalBalAt σ I.codeOwner := by
  have hwf : weth9StorageWF σ I := by
    rcases hsel with h | h
    · exact weth9StorageWF_of_sel (not_selIs_of_selIs h (by native_decide))
        (not_selIs_of_selIs h (by native_decide))
    · exact weth9StorageWF_of_sel (not_selIs_of_selIs h (by native_decide))
        (not_selIs_of_selIs h (by native_decide))
  obtain ⟨hrun⟩ := weth9Correct
  cases hrun σ σ₀ g A I hcode hsize hwf trivial with
  | execution hΞ' hstele hequiv =>
    obtain rfl := hΞ'.symm.trans hΞ
    cases hequiv with
    | success h1 h2 h3 _ =>
      cases h1
      subst h2 h3
      obtain ⟨henv, hcons⟩ := weth9_steleExec_conserves hinj hsel hlt hstele
      rw [totalBal_eq_At, henv] at hcons
      exact hcons
    | revert h1 _ => cases h1
    | noMatch h1 _ => cases h1
    | decodingFailed h1 _ => cases h1
    | invalidHalt h1 _ => cases h1
    | staticHalt h1 _ => cases h1
  | outOfGas hΞ' => cases hΞ'.symm.trans hΞ

end Benchmarks.WETH9.Props
