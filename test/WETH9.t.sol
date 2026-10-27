pragma solidity 0.5.17;

import "../src/WETH9.sol";
import "./Vm.sol";

contract Holder {
    function() external payable {}
}

contract WETH9Test {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    WETH9 weth;
    address payable alice;
    address payable bob;

    function setUp() public {
        weth = new WETH9();
        alice = address(new Holder());
        bob = address(new Holder());
    }

    function testFuzz_DepositWithdraw(uint96 amount, uint96 back) public {
        vm.assume(back <= amount);
        vm.deal(alice, amount);
        vm.startPrank(alice);
        weth.deposit.value(amount)();
        require(weth.balanceOf(alice) == amount, "deposit mints msg.value");
        weth.withdraw(back);
        vm.stopPrank();
        require(weth.balanceOf(alice) == amount - back, "withdraw burns wad");
        require(alice.balance == back, "withdraw sends wad");
        require(weth.totalSupply() == amount - back, "supply is the ETH held");
    }

    function testFuzz_TransferFrom(uint96 amount, uint96 allowed, uint96 moved) public {
        vm.assume(moved <= amount && moved <= allowed);
        vm.deal(alice, amount);
        vm.startPrank(alice);
        weth.deposit.value(amount)();
        weth.approve(bob, allowed);
        vm.stopPrank();
        vm.prank(bob);
        weth.transferFrom(alice, bob, moved);
        require(weth.balanceOf(bob) == moved, "moved");
        require(weth.allowance(alice, bob) == allowed - moved, "allowance spent");
    }

    function test_MaxAllowanceIsNotSpent() public {
        vm.deal(alice, 1 ether);
        vm.startPrank(alice);
        weth.deposit.value(1 ether)();
        weth.approve(bob, uint(-1));
        vm.stopPrank();
        vm.prank(bob);
        weth.transferFrom(alice, bob, 1 ether);
        require(weth.allowance(alice, bob) == uint(-1), "max allowance stays");
    }
}
