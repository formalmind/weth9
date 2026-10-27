# WETH9: properties of the deployed bytecode

The proofs in `formal/` are about a Lean model of `src/WETH9.sol` that formal-ast generates from solc's AST, so they
trust the compiler. The proofs here are about the compiled bytecode itself: they carry two of WETH9's statements down
to it through [EquiVM](https://github.com/argotorg/EquiVM)'s proof that WETH9's bytecode refines its Stele
specification (`Benchmarks.WETH9.weth9ContractCorrect`, the canonical WETH9 compiled with solc 0.5.16, optimizer 200
runs).

EquiVM is pinned in `lakefile.toml`. Build with:

```sh
lake exe cache get   # Mathlib, prebuilt
lake build
```

## Theorems (namespace `Benchmarks.WETH9.Props`)

| Statement | Theorem | On the bytecode |
| --- | --- | --- |
| S-03: `transfer` and `transferFrom` conserve the sum of balances, including a transfer to yourself | `weth9_bytecode_conserves` | Proved |
| S-01: solvency, the sum of balances never exceeds the contract's ETH | `weth9_bytecode_solvent_of_not_withdraw` | Proved for every function but `withdraw`: `deposit`, the fallback, `approve`, `transfer`, `transferFrom` and the getters |
| S-01, every function | `weth9_bytecode_solvent_all` | Proved, with the assumption on `withdraw`'s ETH send below |

Each states: if the EVM runs WETH9's runtime bytecode (`Ξ`) with any accounts, gas, caller, value and calldata, and the
call succeeds, the property holds of the account map it returns.

## Assumptions

- `SlotsInjective`: distinct holders get distinct `balanceOf` slots, and no `allowance` slot is a `balanceOf` slot.
  This is Keccak-256 collision resistance, which EquiVM doesn't assume as an axiom.
- S-03: the balances add up to less than 2^256 before the call. WETH9 is solc 0.5 code, so `balanceOf[dst] + wad`
  wraps; with a larger sum the property would be false. Solvency implies it.
- S-01: the contract is solvent before the call (`Σ balanceOf + msg.value ≤ balance`, stated on `Ξ`'s input, after the
  EVM has credited `msg.value`), and `weth9StorageWF`, the refinement theorem's own condition: `name` and `symbol`
  are stored strings shorter than 2^64 bytes.
- S-01 for `withdraw` only (`CallsKeepSolvent`, `HasCode`): every call WETH9 makes that sends `v` wei while solvent
  returns with WETH9 still solvent. `withdraw` sends ETH to the caller, whose code can call back into WETH9 at any
  depth; discharging this needs an induction over the whole EVM by call depth, which isn't done. Everything else in
  `withdraw` is proved: the `require`, the debit, and both outcomes of the call.

## Trusted base

Lean's kernel and its three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), EquiVM's EVM semantics
(it passes the Ethereum conformance tests), and Lean's compiled evaluator for concrete facts: the theorems depend on
about 2,400 `native_decide` facts, almost all from EquiVM's refinement proof (decoding, selectors, storage slots);
these files add four. No `sorry`, `admit` or new `axiom`.

Written by Formal Mind's agents on top of EquiVM, whose authors are Eleftherios Lazaropoulos and Zoe Paraskevopoulou
("Foundational Refinement Proofs for EVM Bytecode, at the Price of Tokens", arXiv 2607.26306).
