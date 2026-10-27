# Plan

One item per function in scope, from formal-ast: the contracts the Foundry scripts deploy or call, with their bases; the scripts' calls first, then the internal and library functions the model has a def for. `- [x]` is proved on the Proofs page, `- [!]` blocked or a finding.

- [x] `WETH9.approve` — WETH9 (src/WETH9.sol:49): nonpayable · writes [allowance] · guards 0 · external calls 0
- [x] `WETH9.«»` — WETH9 (src/WETH9.sol:31): payable · writes [balanceOf] · guards 0 · external calls 0
- [x] `WETH9.deposit` — WETH9 (src/WETH9.sol:34): payable · writes [balanceOf] · guards 0 · external calls 0
- [x] `WETH9.withdraw` — WETH9 (src/WETH9.sol:38): nonpayable · writes [balanceOf] · guards 1 · external calls 1
- [x] `WETH9.transfer` — WETH9 (src/WETH9.sol:55): nonpayable · writes [balanceOf, allowance] · guards 2 · external calls 0
- [ ] `WETH9.transferFrom` — WETH9 (src/WETH9.sol:59): nonpayable · writes [balanceOf, allowance] · guards 2 · external calls 0
- [ ] `WETH9.totalSupply` — WETH9 (src/WETH9.sol:45): view · writes [] · guards 0 · external calls 0
