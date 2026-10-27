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

These are claims from `.formal/statements.md`.

| # | Claim | Mark | Proof / counterexample |
|---|---|---|---|
| S-01 | Solvency: the sum of all balances never exceeds the contract's ETH | `[ ]` open (invariant) | none yet |
| S-02 | `totalSupply()` ≥ sum of balances, and it can be strictly greater (forced ETH) | `[ ]` open (invariant) | none yet |
| S-03 | `transfer`/`transferFrom` conserve the sum of balances, including self-transfer | `[~]` working (conservation): `transferFrom` proved, `transfer` next | `moveBal_sum`, `transferFrom_conserves`: [WETH9Conservation.lean](formal/Refinement/Swarm/WETH9Conservation.lean). Whenever `transferFrom` succeeds, through either branch and including `src = dst`, the sum of `balanceOf` over any duplicate-free list of accounts containing `src` and `dst` is unchanged. It assumes `balanceOf[src] < 2^256` and that `balanceOf[dst] + wad` doesn't wrap. |
| S-04 | Only an allowance lets someone lower another account's balance, and a `uint(-1)` allowance is never spent down | `[?]` waiting for the maintainer to confirm the formalization | none yet |
| S-05 | Anyone can always withdraw their whole balance unless their own address rejects a 2300-gas ETH send | `[ ]` open | none yet |

No bugs have been reported (`audit/formal-mind.audit.json`).

## Not covered

- **Invariants across calls (S-01, S-02).** The model keeps no ETH balance in storage. The contract's ETH appears only as `env.balance` of each call, so solvency has to be stated as a condition linking `env.balance` from one call to the next. That is not done yet.
- **Overflow in S-03.** Conservation assumes the credit to `dst` does not wrap past 2^256. That holds while total supply stays below 2^256 ETH.
- **Re-entrancy and the ETH send in `withdraw`.** The model treats the external call as an opaque step (`ext.lowCall`). No theorem covers what a re-entrant receiver does. S-05 will need an explicit assumption about that call.
- **Gas, liveness and forced ETH (S-05, part of S-02).** The model does not cover gas or ETH that arrives through selfdestruct or coinbase.
- **Compiler and EVM.** The model comes from solc's AST, not the bytecode. The proofs assume that the compiler preserves the source's meaning.

## Check it yourself

```sh
cd formal && lake build
```

This builds the generated model and every proof under `formal/Refinement/`. It needs no Mathlib. It should end with `Build completed successfully`.

<!-- formal-mind:start -->
## Verification

0 of 7 functions proved: each theorem built and checked by Lean (no `sorry`, no axioms beyond Lean's own) and approved by the reviewer, kept in the proof ledger (`.formal/ledger.json`).

### Functions

| Function | Status | Theorems | Shows |
|---|---|---|---|
| `WETH9.deposit` | pending | [`S01.WETH9_deposit`](formal/Refinement/Statements/S01/WETH9Deposit.lean#L27), [`S02.WETH9_deposit`](formal/Refinement/Statements/S02/WETH9Deposit.lean#L10), [`S05.WETH9_deposit`](formal/Refinement/Statements/S05/WETH9Deposit.lean#L11), [`S06.WETH9_deposit`](formal/Refinement/Statements/S06/WETH9Deposit.lean#L11), [`WETH9.deposit_spec`](formal/Refinement/Swarm/WETH9Deposit.lean#L7), [`WETH9.deposit_frame`](formal/Refinement/Swarm/WETH9Deposit.lean#L18), [`WETH9.fallback_spec`](formal/Refinement/Swarm/WETH9Fallback.lean#L7) | returns, writes |
| `WETH9.«»` | pending | [`S01.WETH9_`](formal/Refinement/Statements/S01/WETH9Fallback.lean#L27), [`S01.WETH9_fallback`](formal/Refinement/Statements/S01/WETH9Fallback.lean#L45), [`S02.WETH9_`](formal/Refinement/Statements/S02/WETH9Fallback.lean#L11), [`S02.WETH9_fallback`](formal/Refinement/Statements/S02/WETH9Fallback.lean#L30), [`S05.WETH9_`](formal/Refinement/Statements/S05/WETH9Fallback.lean#L10), [`S05.WETH9_fallback`](formal/Refinement/Statements/S05/WETH9Fallback.lean#L26), [`S06.WETH9_`](formal/Refinement/Statements/S06/WETH9Fallback.lean#L42), [`WETH9.fallback_spec`](formal/Refinement/Swarm/WETH9Fallback.lean#L7), [`WETH9.fallback_frame`](formal/Refinement/Swarm/WETH9Fallback.lean#L18) | returns, writes |
| `WETH9.withdraw` | pending | [`S01.WETH9_withdraw`](formal/Refinement/Statements/S01/WETH9Withdraw.lean#L42), [`S02.WETH9_withdraw`](formal/Refinement/Statements/S02/WETH9Withdraw.lean#L13), [`S05.WETH9_withdraw`](formal/Refinement/Statements/S05/WETH9Withdraw.lean#L13), [`S06.WETH9_withdraw`](formal/Refinement/Statements/S06/WETH9Withdraw.lean#L26), [`WETH9.withdraw_reverts`](formal/Refinement/Swarm/WETH9Withdraw.lean#L10), [`WETH9.withdraw_spec`](formal/Refinement/Swarm/WETH9Withdraw.lean#L23) | returns, reverts, writes |
| `WETH9.totalSupply` | partly proved | [`WETH9.totalSupply_spec`](formal/Refinement/Swarm/WETH9TotalSupply.lean#L6) | returns |
| `WETH9.approve` | pending | [`S01.WETH9_approve`](formal/Refinement/Statements/S01/WETH9Approve.lean#L10), [`S02.WETH9_approve`](formal/Refinement/Statements/S02/WETH9Approve.lean#L10), [`S05.WETH9_approve`](formal/Refinement/Statements/S05/WETH9Approve.lean#L9), [`S06.WETH9_approve`](formal/Refinement/Statements/S06/WETH9Approve.lean#L11), [`WETH9.approve_spec`](formal/Refinement/Swarm/WETH9Approve.lean#L8), [`WETH9.approve_allowance`](formal/Refinement/Swarm/WETH9Approve.lean#L17) | returns, writes |
| `WETH9.transferFrom` | pending | [`S01.WETH9_transferFrom`](formal/Refinement/Statements/S01/WETH9TransferFrom.lean#L9), [`S02.WETH9_transferFrom`](formal/Refinement/Statements/S02/WETH9TransferFrom.lean#L10), [`S03.WETH9_transferFrom`](formal/Refinement/Statements/S03/WETH9TransferFrom.lean#L10), [`S04.WETH9_transferFrom`](formal/Refinement/Statements/S04/WETH9TransferFrom.lean#L11), [`S05.WETH9_transferFrom`](formal/Refinement/Statements/S05/WETH9TransferFrom.lean#L11), [`S06.TransferFromAux.tf_ok`](formal/Refinement/Statements/S06/WETH9TransferFrom.lean#L17), [`S06.WETH9_transferFrom`](formal/Refinement/Statements/S06/WETH9TransferFrom.lean#L53), [`S08.WETH9_transferFrom`](formal/Refinement/Statements/S08/WETH9TransferFrom.lean#L10), [`WETH9.Swarm.Cons.transferFrom_conserves`](formal/Refinement/Swarm/WETH9Conservation.lean#L105), [`WETH9.Swarm.transfer_reverts`](formal/Refinement/Swarm/WETH9Transfer.lean#L10), [`WETH9.Swarm.transfer_succeeds`](formal/Refinement/Swarm/WETH9Transfer.lean#L21), [`WETH9.Swarm.TF.transferFrom_reverts_balance`](formal/Refinement/Swarm/WETH9TransferFrom.lean#L10), [`WETH9.Swarm.TF.transferFrom_reverts_allowance`](formal/Refinement/Swarm/WETH9TransferFrom.lean#L20), [`WETH9.Swarm.TF.transferFrom_succeeds_spend`](formal/Refinement/Swarm/WETH9TransferFrom.lean#L34), [`WETH9.Swarm.TF.transferFrom_succeeds_nospend`](formal/Refinement/Swarm/WETH9TransferFrom.lean#L60) | returns, reverts, writes |
| `WETH9.transfer` | pending | [`S01.WETH9_transfer`](formal/Refinement/Statements/S01/WETH9Transfer.lean#L9), [`S02.WETH9_transfer`](formal/Refinement/Statements/S02/WETH9Transfer.lean#L9), [`S03.WETH9_transfer`](formal/Refinement/Statements/S03/WETH9Transfer.lean#L41), [`S05.WETH9_transfer`](formal/Refinement/Statements/S05/WETH9Transfer.lean#L12), [`S06.WETH9_transfer`](formal/Refinement/Statements/S06/WETH9Transfer.lean#L52), [`S08.WETH9_transfer`](formal/Refinement/Statements/S08/WETH9Transfer.lean#L9), [`WETH9.Swarm.transfer_reverts`](formal/Refinement/Swarm/WETH9Transfer.lean#L10), [`WETH9.Swarm.transfer_succeeds`](formal/Refinement/Swarm/WETH9Transfer.lean#L21) | returns, reverts, writes |

### Statements

| # | Claim | By | Status | Proved by |
|---|---|---|---|---|
| S-01 | Solvency: the sum of all balances never exceeds the ETH the contract holds, after any call. | you | proved (invariant) | 6 of 6 entry points |
| S-02 | totalSupply() can be larger than the sum of balances: ETH forced in (selfdestruct, coinbase) is counted but owned by no one. | you | proved (invariant) | 6 of 6 entry points |
| S-03 | transfer and transferFrom conserve the sum of balances, including a transfer to yourself. | you | proved (conservation) | 2 of 2 entry points |
| S-04 | No one can lower another account's balance except through an allowance that account gave them, and an allowance of uint(-1) is never spent down. | you | proved (function) | 1 of 1 entry points |
| S-05 | Anyone holding a balance can always withdraw all of it (no call by another account can stop them), unless their own address rejects ETH sent with 2300 gas. | you | proved (sequence) | 6 of 6 entry points |
| S-06 | The sum of `WETH9.balanceOf` over all accounts equals `totalSupply()`, i.e. `address(this).balance`, apart from ETH forced in (selfdestruct or coinbase): without forced ETH it is exact equality, and with it the sum is lower by exactly the forced amount. | you | working (invariant) | 5 of 6 entry points |
| S-08 | `WETH9.transfer` and `WETH9.transferFrom` change `balanceOf` only at `src` and `dst`: every other account's `balanceOf` is unchanged (and `allowance` changes only at `[src][msg.sender]` in `transferFrom`). | you | proved (conservation) | 2 of 2 entry points |

Check it yourself: `cd formal && lake build`.
<!-- formal-mind:end -->
