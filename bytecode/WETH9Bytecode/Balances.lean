import Benchmarks.WETH9.Correct
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# WETH9 — `balanceOf` readers, the sum of balances, and storage frame lemmas

The foundation for the WETH9 properties of `Proofs.WETH9.Conservation` (S-03) and
`Proofs.WETH9.Solvency` (S-01), in the style of `Proofs.ERC20.Balances`: nothing here talks
about bytecode, only about the Stele spec's effect on the contract's storage.

* `balOf evm a` — `balanceOf[a]` read from the contract's own account, as `ℕ`;
* `totalBal evm` — `Σ_a balanceOf[a]` over *all* addresses (a `Finset.univ` sum: `AccountAddress`
  is finite);
* `SlotsInjective` — the explicit storage-layout hypothesis: distinct holders have distinct
  `balanceOf` slots, and no `allowance` slot is a `balanceOf` slot.  For Solidity's layout this is
  Keccak collision-freedom, which the repo does not axiomatize (as `ERC20.InjectiveLayout`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open scoped BigOperators

namespace Benchmarks.WETH9.Props

open Benchmarks.WETH9

/-! ## Readers -/

/-- `balanceOf[a]` in the storage of the state's own contract (`codeOwner`), as a `ℕ`. -/
def balOf (evm : EVM.State) (a : AccountAddress) : ℕ :=
  (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (balanceOfSlot (.address a))).toNat

/-- `Σ_a balanceOf[a]`, over every address. -/
noncomputable def totalBal (evm : EVM.State) : ℕ :=
  ∑ a : AccountAddress, balOf evm a

/-! ## The layout hypothesis -/

/-- Keccak collision-freedom, as WETH9's layout uses it: `balanceOf` slots are injective in the
    holder, and an `allowance` slot is never a `balanceOf` slot.  Kept a named hypothesis. -/
def SlotsInjective : Prop :=
  (∀ a b : AccountAddress, balanceOfSlot (.address a) = balanceOfSlot (.address b) → a = b) ∧
  (∀ o s a : AccountAddress, allowanceSlot (.address o) (.address s) ≠ balanceOfSlot (.address a))

/-! ## Frame lemmas -/

theorem balOf_of_accountMap {evm evm' : EVM.State} (hco : evm'.executionEnv = evm.executionEnv)
    (hσ : evm'.accountMap = evm.accountMap) : balOf evm' = balOf evm := by
  funext a
  simp only [balOf, Stele.EVM.storageLoad, State.lookupAccount, hco, hσ]

/-- A store to a slot that is no `balanceOf` slot leaves every balance unchanged. -/
theorem balOf_storageStore_other (evm : EVM.State) (k v : UInt256)
    (hk : ∀ a : AccountAddress, balanceOfSlot (.address a) ≠ k) :
    balOf (Stele.EVM.storageStore evm evm.executionEnv.codeOwner k v) = balOf evm := by
  funext a
  simp only [balOf, storageStore_executionEnv]
  rw [storageLoad_storageStore_ne _ _ (hk a)]

/-- A store to the contract's `balanceOf[x]` slot updates exactly `x`'s balance (the account
    exists). -/
theorem balOf_storageStore_bal (hinj : SlotsInjective) (evm : EVM.State) (x : AccountAddress)
    (v : UInt256) {acc : Account} (hex : evm.accountMap.get? evm.executionEnv.codeOwner = some acc) :
    balOf (Stele.EVM.storageStore evm evm.executionEnv.codeOwner (balanceOfSlot (.address x)) v) =
      Function.update (balOf evm) x v.toNat := by
  funext a
  by_cases hax : a = x
  · subst hax
    simp only [balOf, storageStore_executionEnv, Function.update_self]
    rw [storageLoad_storageStore_same_present _ _ hex]
  · simp only [balOf, storageStore_executionEnv, Function.update_of_ne hax]
    rw [storageLoad_storageStore_ne _ _ (fun h => hax (hinj.1 _ _ h))]

/-- A store to a missing account is a no-op. -/
theorem storageStore_missing (evm : EVM.State) (k v : UInt256)
    (hmiss : evm.accountMap.get? evm.executionEnv.codeOwner = none) :
    Stele.EVM.storageStore evm evm.executionEnv.codeOwner k v = evm :=
  storageStore_absent evm _ hmiss k v

/-- A store to an existing account leaves it existing. -/
theorem storageStore_present (evm : EVM.State) (k v : UInt256) {acc : Account}
    (hex : evm.accountMap.get? evm.executionEnv.codeOwner = some acc) :
    ∃ acc', (Stele.EVM.storageStore evm evm.executionEnv.codeOwner k v).accountMap.get?
      (Stele.EVM.storageStore evm evm.executionEnv.codeOwner k v).executionEnv.codeOwner =
        some acc' := by
  refine ⟨acc.updateStorage k v, ?_⟩
  rw [storageStore_executionEnv]
  simp only [Stele.EVM.storageStore, State.lookupAccount, State.setAccount, hex, Option.option]
  simp [Std.ExtTreeMap.get?_eq_getElem?]

/-- The contract's account exists. -/
def Present (evm : EVM.State) : Prop :=
  ∃ acc, evm.accountMap.get? evm.executionEnv.codeOwner = some acc

theorem present_storageStore (evm : EVM.State) (k v : UInt256) :
    Present (Stele.EVM.storageStore evm evm.executionEnv.codeOwner k v) ↔ Present evm := by
  cases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none => rw [storageStore_missing evm k v hacc]
  | some acc =>
    exact ⟨fun _ => ⟨acc, hacc⟩, fun _ => storageStore_present evm k v hacc⟩

theorem not_present (evm : EVM.State) (h : ¬ Present evm) :
    evm.accountMap.get? evm.executionEnv.codeOwner = none := by
  cases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => exact absurd ⟨acc, hacc⟩ h

theorem balOf_lt (evm : EVM.State) (a : AccountAddress) : balOf evm a < UInt256.size :=
  (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (balanceOfSlot (.address a))).val.isLt

/-! ## The contract's ETH balance -/

/-- The ETH balance of `a` in `σ` (`0` for a missing account), as a `ℕ`. -/
def ethBalAt (σ : AccountMap) (a : AccountAddress) : ℕ :=
  (σ.get? a).elim 0 (fun acc => acc.balance.toNat)

/-- The ETH balance of the state's own contract. -/
def ethBal (evm : EVM.State) : ℕ := ethBalAt evm.accountMap evm.executionEnv.codeOwner

/-- `a`'s account exists and holds the WETH9 runtime code. -/
def HasCode (σ : AccountMap) (a : AccountAddress) : Prop :=
  ∃ acc, σ.get? a = some acc ∧ acc.code = weth9Bytecode

theorem ethBal_lt (evm : EVM.State) : ethBal evm < UInt256.size := by
  unfold ethBal ethBalAt
  cases evm.accountMap.get? evm.executionEnv.codeOwner with
  | none => decide
  | some acc => exact acc.balance.val.isLt

/-- Storage writes leave the contract's ETH balance unchanged. -/
theorem ethBal_storageStore (evm : EVM.State) (k v : UInt256) :
    ethBal (Stele.EVM.storageStore evm evm.executionEnv.codeOwner k v) = ethBal evm := by
  cases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none => rw [storageStore_missing _ _ _ hacc]
  | some acc =>
    unfold ethBal ethBalAt
    rw [storageStore_executionEnv, hacc]
    simp only [Stele.EVM.storageStore, State.lookupAccount, State.setAccount, hacc, Option.option]
    simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self, Option.elim]
    unfold Account.updateStorage
    split <;> rfl

/-- Storage writes keep the contract's code. -/
theorem hasCode_storageStore (evm : EVM.State) (k v : UInt256)
    (h : HasCode evm.accountMap evm.executionEnv.codeOwner) :
    HasCode (Stele.EVM.storageStore evm evm.executionEnv.codeOwner k v).accountMap
      evm.executionEnv.codeOwner := by
  obtain ⟨acc, hacc, hc⟩ := h
  refine ⟨acc.updateStorage k v, ?_, ?_⟩
  · simp only [Stele.EVM.storageStore, State.lookupAccount, State.setAccount, hacc, Option.option]
    simp [Std.ExtTreeMap.get?_eq_getElem?]
  · unfold Account.updateStorage; split <;> exact hc

/-! ## Sums -/

/-- Moving `v` from `x` to `y ≠ x` (`v ≤ f x`) leaves the total unchanged. -/
theorem sum_transfer_eq {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) {x y : α}
    (hxy : x ≠ y) (v : ℕ) (hv : v ≤ f x) :
    (∑ a, Function.update (Function.update f x (f x - v)) y (f y + v) a) = ∑ a, f a := by
  have hx' : x ∈ (Finset.univ : Finset α) \ {y} :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, by simp [hxy]⟩
  rw [Finset.sum_update_of_mem (Finset.mem_univ y), Finset.sum_update_of_mem hx']
  have hRy : (∑ a, f a) = f y + ∑ a ∈ (Finset.univ : Finset α) \ {y}, f a := by
    rw [← Finset.sum_update_of_mem (Finset.mem_univ y) f (f y), Function.update_eq_self]
  have hRx : (∑ a ∈ (Finset.univ : Finset α) \ {y}, f a)
      = f x + ∑ a ∈ ((Finset.univ : Finset α) \ {y}) \ {x}, f a := by
    rw [← Finset.sum_update_of_mem hx' f (f x), Function.update_eq_self]
  rw [hRy, hRx]
  omega

/-- Two distinct summands are at most the total. -/
theorem add_le_sum {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) {x y : α} (hxy : x ≠ y) :
    f x + f y ≤ ∑ a, f a := by
  rw [← Finset.sum_pair hxy]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Changing one summand changes the total by the difference. -/
theorem sum_update_add {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (x : α) (n : ℕ) :
    (∑ a, Function.update f x n a) + f x = (∑ a, f a) + n := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ x)]
  have h : (∑ a, f a) = f x + ∑ a ∈ (Finset.univ : Finset α) \ {x}, f a := by
    rw [← Finset.sum_update_of_mem (Finset.mem_univ x) f (f x), Function.update_eq_self]
  rw [h]; omega

theorem single_le_sum {α : Type*} [Fintype α] (f : α → ℕ) (x : α) : f x ≤ ∑ a, f a :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)

end Benchmarks.WETH9.Props
