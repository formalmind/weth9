pragma solidity 0.5.17;

/// The few Foundry cheatcodes the tests use (forge-std needs solc >=0.6.2).
interface Vm {
    function deal(address who, uint256 amount) external;
    function prank(address sender) external;
    function startPrank(address sender) external;
    function stopPrank() external;
    function assume(bool condition) external;
}
