pragma solidity 0.5.17;

import "../src/WETH9.sol";

/// Deploys WETH9 as mainnet did: a bare `new`, no constructor arguments. This script is what puts WETH9 in scope.
contract Deploy {
    function run() public returns (WETH9) {
        return new WETH9();
    }
}
