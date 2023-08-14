// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.0;

import "../../contracts/bank/StrictBank.sol";

contract StrictBankHarness is StrictBank {

    constructor(RoleStore _roleStore, DataStore _dataStore) StrictBank(_roleStore, _dataStore) {}

    bytes32 public constant WNT = keccak256(abi.encode("WNT"));
    bytes32 public constant HOLDING_ADDRESS = keccak256(abi.encode("HOLDING_ADDRESS"));
    bytes32 public constant CONTROLLER = keccak256(abi.encode("CONTROLLER"));
    bytes32 public constant TOKEN_TRANSFER_GAS_LIMIT = keccak256(abi.encode("TOKEN_TRANSFER_GAS_LIMIT"));

    function afterTransferOut(address token) external {
        _afterTransferOut(token);
    }

    function getETHBalance(address account) external returns(uint256) {
        return account.balance;
    }

    function tokenTransferGasLimit(address token) external pure returns (bytes32) {
        return keccak256(abi.encode(
            TOKEN_TRANSFER_GAS_LIMIT,
            token
        ));
    }
}
