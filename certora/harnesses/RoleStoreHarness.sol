// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.0;

import "../../contracts/role/RoleStore.sol";
import "@openzeppelin/contracts/utils/structs/EnumerableSet.sol";

contract RoleStoreHarness is RoleStore {

    bytes32 public constant ROLE_ADMIN = keccak256(abi.encode("ROLE_ADMIN"));
    bytes32 public constant TIMELOCK_MULTISIG = keccak256(abi.encode("TIMELOCK_MULTISIG"));

    using EnumerableSet for EnumerableSet.AddressSet;

    function containsRole(address account, bytes32 roleKey) public view returns (bool) {
        return roleMembers[roleKey].contains(account);
    }

    function containsRoleInCache(address account, bytes32 roleKey) public view returns (bool) {
        return roleCache[account][roleKey];
    }

    function getMembersLength(bytes32 roleKey) external view returns (uint256) {
        return roleMembers[roleKey].length();
    }

    function getRoleMemberByIndex(bytes32 roleKey, uint256 index) external view returns (address) {
        return roleMembers[roleKey].at(index);
    }
}
