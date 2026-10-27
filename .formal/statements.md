# Statements

Claims about the code in plain words, each proved or disproved by the swarm: `- [ ]` open, `- [~]` working, `- [x]` proved, `- [!]` disproved, `- [?]` waiting for you, `- [-]` can't be proved against this model. Add your own as `- [ ] <the claim>`; the indented lines under each one are the swarm's.

- [ ] S-01 · you · Solvency: the sum of all balances never exceeds the ETH the contract holds, after any call.
  - kind: invariant
  - note: the swarm proves function and access statements so far; invariant statements come later
  - means: In every reachable state of WETH9, the sum of `balanceOf[a]` over all addresses a is at most the contract's own ETH balance (`address(this).balance`). It must hold initially and be preserved by every external entry point: the receive/fallback, `deposit`, `withdraw`, `transfer`, `transferFrom` and `approve`, including when `withdraw`'s ETH send re-enters the contract.
  - assumes: ETH that arrives with no call (selfdestruct, coinbase) or is held before deployment only raises the contract's balance, so it keeps the inequality as ≤; it is not claimed to be equality
  - assumes: Sums are taken over unbounded integers, not uint256, so overflow of the sum itself is not hidden
  - assumes: 'After any call' means after each top-level transaction to WETH9, measured on its final state
- [ ] S-02 · you · totalSupply() can be larger than the sum of balances: ETH forced in (selfdestruct, coinbase) is counted but owned by no one.
  - kind: invariant
  - note: the swarm proves function and access statements so far; invariant statements come later
  - means: In every reachable state of WETH9, totalSupply() (which returns the contract's ETH balance, address(this).balance) is greater than or equal to the sum of balanceOf over all addresses. The two can differ: ETH that arrives without calling deposit/fallback (selfdestruct to the contract, coinbase/block reward, or pre-deployment funding) raises totalSupply but credits no balanceOf. So the claim is the inequality ≥, together with the fact that strict > is reachable, not equality.
  - assumes: totalSupply() returns address(this).balance, as in canonical WETH9
  - assumes: ETH can only leave the contract through withdraw, which first reduces balanceOf[msg.sender] by the same amount
  - assumes: Forced ETH (selfdestruct/coinbase) is modeled as an arbitrary increase of the contract balance between calls
- [ ] S-03 · you · transfer and transferFrom conserve the sum of balances, including a transfer to yourself.
  - kind: conservation
  - note: the swarm proves function and access statements so far; conservation statements come later
  - means: For every successful (non-reverting) call to WETH9.transfer(dst, wad) and WETH9.transferFrom(src, dst, wad), the sum of balanceOf over all addresses is the same after the call as before. This includes src == dst, where the balance of that address is unchanged. transfer just calls transferFrom(msg.sender, …), so both are covered. Calls that revert change nothing.
  - assumes: The sum is over all addresses, not over a fixed set of holders
  - assumes: Only successful calls are considered; the require balanceOf[src] >= wad ensures the unchecked balanceOf[dst] += wad cannot overflow, given the total supply fits in uint256
  - assumes: This says nothing about allowance or about how totalSupply (address(this).balance) relates to the sum of balances
- [?] S-04 · you · No one can lower another account's balance except through an allowance that account gave them, and an allowance of uint(-1) is never spent down.
  - note: couldn't formalize it: Nothing needs redoing. The S-04 formalization was recorded before the app quit, so it's still waiting for your confirmation and the swarm will start proving it once you confirm. The formalization is about `WETH9.transferFrom`: - Suppose someone other than `src` calls it, the call succeeds and `src`'
- [ ] S-05 · you · Anyone holding a balance can always withdraw all of it (no call by another account can stop them), unless their own address rejects ETH sent with 2300 gas.
  - kind: sequence
  - note: the swarm proves function and access statements so far; sequence statements come later
  - means: Take any account A with balanceOf[A] = b. Whatever other accounts call before it (deposit, withdraw, transfer, transferFrom, approve), A can still call WETH9.withdraw(balanceOf[A]) and it succeeds: it zeroes balanceOf[A] and sends that amount of ETH to A. It only reverts if A's own address rejects the ETH or uses more than the 2300 gas that transfer forwards. This needs two things: the contract always holds at least the sum of all balances in ETH, so the transfer is never short; and no other account can lower balanceOf[A], except a spender A approved, through transferFrom.
  - assumes: Spending by an account A approved through transferFrom counts as A's own choice, not as another account stopping A. Such a spender can lower balanceOf[A], so this case is left out of the claim.
  - assumes: The claim is about the amount A holds at the moment A withdraws. A can't be stopped from withdrawing that amount; the claim doesn't promise the balance A held earlier.
  - assumes: A's withdraw transaction has enough gas, and EVM-level failures such as the call-depth limit are left out.
  - assumes: The contract's ETH balance is always at least the sum of balanceOf. ETH forced in by selfdestruct only adds to it.
<!-- next: S-06 -->
