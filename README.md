# WETH9, formally checked

WETH9 is the canonical Wrapped Ether contract (`src/WETH9.sol`). You send it ETH and it records an equal ERC-20 balance for you. `withdraw` burns that balance and sends the ETH back. `totalSupply()` returns the ETH the contract holds.

[Formal Mind](https://formal.team) generated a Lean model of every WETH9 function from solc's AST (`formal/Generated/WETH9.lean`). It then proved what each function does, in Lean 4 with no `sorry`, no `admit`, no `native_decide` and no new axioms. The proofs are in [`formal/Refinement/Swarm/`](formal/Refinement/Swarm/).

## Functions

Every function in scope is **proved** in the proof ledger (`.formal/ledger.json`): each theorem built and checked by Lean, and approved by the reviewer. No function is partly proved or pending.

| Function | Status | Theorems | What it shows |
|---|---|---|---|
| `receive`/fallback (`WETH9.sol:31`) | proved | `fallback_spec`, `fallback_frame`: [WETH9Fallback.lean](formal/Refinement/Swarm/WETH9Fallback.lean) | It never reverts and only credits `msg.value` to the sender's balance. |
| `deposit` (`:34`) | proved | `deposit_spec`, `deposit_frame`: [WETH9Deposit.lean](formal/Refinement/Swarm/WETH9Deposit.lean) | It never reverts, credits `msg.value` (mod 2^256) to `balanceOf[msg.sender]` and changes nothing else. |
| `withdraw` (`:38`) | proved | `withdraw_reverts`, `withdraw_spec`, `withdraw_sub_exact`: [WETH9Withdraw.lean](formal/Refinement/Swarm/WETH9Withdraw.lean) | It reverts if the balance is below `wad`. Otherwise it subtracts exactly `wad` (no wraparound) before sending the ETH. |
| `totalSupply` (`:45`) | proved | `totalSupply_spec`: [WETH9TotalSupply.lean](formal/Refinement/Swarm/WETH9TotalSupply.lean) | It returns the contract's ETH balance and changes no state. |
| `approve` (`:49`) | proved | `approve_spec`, `approve_allowance`: [WETH9Approve.lean](formal/Refinement/Swarm/WETH9Approve.lean) | It sets `allowance[msg.sender][guy] = wad`, returns true and writes nothing else. |
| `transfer` (`:55`) | proved | `transfer_reverts`, `transfer_succeeds`: [WETH9Transfer.lean](formal/Refinement/Swarm/WETH9Transfer.lean) | It behaves as `transferFrom(msg.sender, dst, wad)`: it reverts on insufficient balance, otherwise it moves `wad`. |
| `transferFrom` (`:59`) | proved | `transferFrom_reverts_balance`, `transferFrom_reverts_allowance`, `transferFrom_succeeds_spend`, `transferFrom_succeeds_nospend`: [WETH9TransferFrom.lean](formal/Refinement/Swarm/WETH9TransferFrom.lean) | It reverts on low balance, or on low finite allowance when the caller is a third party. Otherwise it moves `wad`, and spends the allowance only when the caller is a third party whose allowance is not `uint(-1)`. |

The function theorems are stated over an abstract storage accessor `ext`. Where a theorem relies on storage behaving as storage, it assumes that reading back a written state returns it (`ext.get (ext.set w s) = s`), and in `transferFrom` that the last write wins.

## Statements

These are claims from `.formal/statements.md`. None is proved or disproved yet.

| # | Claim | Mark | Proof / counterexample |
|---|---|---|---|
| S-01 | Solvency: the sum of all balances never exceeds the contract's ETH | `[ ]` open (invariant) | none yet |
| S-02 | `totalSupply()` ≥ sum of balances, and it can be strictly greater (forced ETH) | `[ ]` open (invariant) | none yet |
| S-03 | `transfer`/`transferFrom` conserve the sum of balances, including self-transfer | `[ ]` open (conservation) | none yet |
| S-04 | Only an allowance lets someone lower another account's balance, and a `uint(-1)` allowance is never spent down | `[?]` waiting for the maintainer to confirm the formalization | none yet |
| S-05 | Anyone can always withdraw their whole balance unless their own address rejects a 2300-gas ETH send | `[ ]` open | none yet |

No bugs have been reported (`audit/formal-mind.audit.json`).

## Not covered

- **Invariants and conservation across calls (S-01, S-02, S-03).** The proofs describe each call on its own. None of them sums balances over all addresses or follows state across a sequence of transactions. Formal Mind's pipeline handles invariant and conservation statements in a later stage.
- **Re-entrancy and the ETH send in `withdraw`.** The model treats the external call as an opaque step. No theorem covers what a re-entrant receiver does.
- **Gas, liveness and forced ETH (S-05, part of S-02).** The model does not cover gas or ETH that arrives through selfdestruct or coinbase.
- **Compiler and EVM.** The model comes from solc's AST, not the bytecode. The proofs assume that the compiler preserves the source's meaning.

## Check it yourself

```sh
cd formal && lake build
```

This builds the generated model and every proof under `formal/Refinement/`. It needs no Mathlib. It should end with `Build completed successfully`.
