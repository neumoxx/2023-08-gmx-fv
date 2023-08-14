using Role as Role;

// METHOD specification
methods {
    function grantRole(address, bytes32) external;
    function revokeRole(address, bytes32) external;
    function hasRole(address, bytes32) external returns (bool);
    function containsRole(address, bytes32) external returns (bool);
    function containsRoleInCache(address, bytes32) external returns (bool);
    function getRoleCount() external returns (uint256) envfree;
    function getRoles(uint256, uint256) external returns (bytes32[]) envfree;
    function getRoleMemberCount(bytes32) external returns (uint256) envfree;
    function getRoleMembers(bytes32, uint256, uint256) external returns (address[]) envfree;
    function _grantRole(address, bytes32) internal;
    function _revokeRole(address, bytes32) internal;
    function ROLE_ADMIN() external returns (bytes32) envfree;
    function Role.ROLE_ADMIN() external returns (bytes32);
    function TIMELOCK_MULTISIG() external returns (bytes32) envfree;
}


// DEFINITION

// Returns, whether a value is in the roles set.
definition inRolesSet(bytes32 value) returns bool = (rolesGhostIndexes[value] != 0);

// Returns, whether a value is in the roleMembers set.
definition inRoleMembersSet(bytes32 roleKey, bytes32 value) returns bool = (roleMembersGhostIndexes[roleKey][value] != 0);

/// @notice Functions defined in harness contract
definition notHarnessCall(method f) returns bool =
    (f.selector != sig:containsRole(address,bytes32).selector
    && f.selector != sig:containsRoleInCache(address,bytes32).selector
    && f.selector != sig:getMembersLength(bytes32).selector
    && f.selector != sig:getRoleMemberByIndex(bytes32, uint256).selector);


// RULES


rule grantRoleConsistencyCheck(env e) {

  address account;
  bytes32 roleKey;

  bool isAdmin = hasRole(e, e.msg.sender, ROLE_ADMIN());

  grantRole@withrevert(e, account, roleKey);
  bool lastRev = lastReverted;

  assert lastRev <=> e.msg.value > 0 || !isAdmin, "grantRole not payable and only callable by admin";
  assert !lastRev => (
    containsRole(e, account, roleKey) == true &&
    containsRoleInCache(e, account, roleKey) == true
  );
}


rule revokeRoleConsistencyCheck(env e) {

  address account;
  bytes32 roleKey;

  bool isAdmin = hasRole(e, e.msg.sender, ROLE_ADMIN());
  uint256 lengthPre = getRoleCount@withrevert();

  revokeRole@withrevert(e, account, roleKey);
  bool lastRev = lastReverted;

  assert lastRev <=> (
    e.msg.value > 0 ||
    !isAdmin ||
    (lengthPre == 0 && (roleKey == ROLE_ADMIN() || roleKey == TIMELOCK_MULTISIG()))
  ), "grantRole not payable and only callable by admin";
  assert !lastRev => (
    containsRole(e, account, roleKey) == false &&
    containsRoleInCache(e, account, roleKey) == false
  );
}

rule hasRoleConsistencyCheck(env e) {

  address account;
  bytes32 roleKey;

  bool hasIt = hasRole@withrevert(e, account, roleKey);

  assert lastReverted <=> e.msg.value > 0;
  assert !lastReverted => (
    containsRole(e, account, roleKey) == hasIt &&
    containsRoleInCache(e, account, roleKey) == hasIt
  );

}

rule getRoleCountConsistencyCheck(env e) {

  uint256 length = getRoleCount@withrevert();

  assert !lastReverted;
  assert rolesGhostLength == length;

}

rule getRolesConsistencyCheck(env e) {

  uint256 start;
  uint256 end;

  require end - start == 2;
  require end < getRoleCount();

  bytes32[] roles = getRoles@withrevert(start, end);

  assert start > end <=> lastReverted;
  assert !lastReverted <=> (
    roles[0] == rolesGhostValues[start] &&
    roles[1] == rolesGhostValues[start + 1]
  );

}

rule getRoleMemberCountConsistencyCheck(env e) {

  bytes32 roleKey;

  uint256 length = getRoleMemberCount@withrevert(roleKey);

  assert !lastReverted;
  assert getMembersLength(e, roleKey) == length;

}

rule getRoleMembersConsistencyCheck(env e) {

  bytes32 roleKey;
  uint256 start;
  uint256 end;

  require end - start == 2;
  require end < getRoleMemberCount(roleKey);

  address[] members = getRoleMembers@withrevert(roleKey, start, end);

  assert lastReverted <=> end < start;
  assert !lastReverted => (
        members[0] == getRoleMemberByIndex(e, roleKey, start) &&
        members[1] == getRoleMemberByIndex(e, roleKey, assert_uint256(start + 1))
  );

}


rule roleCountMonotonicallyIncreases(method f) filtered {
    f -> notHarnessCall(f)
} {
    env e;

    uint256 lengthPre = getRoleCount@withrevert();

    calldataarg args;
    f(e, args);

    uint256 lengthPost = getRoleCount@withrevert();

    assert lengthPost >= lengthPre;
}


rule sanity_satisfy(method f) {
    env e;
    calldataarg args;
    f(e, args);
    satisfy true;
}


// GHOST COPIES:
// For every storage variable we add a ghost field that is kept synchronized by hooks.
// The ghost fields can be accessed by the spec, even inside quantifiers.

// roles

// ghost field for the values array
ghost mapping(mathint => bytes32) rolesGhostValues {
    init_state axiom forall mathint x. rolesGhostValues[x] == to_bytes32(0);
}
// ghost field for the indexes map
ghost mapping(bytes32 => uint256) rolesGhostIndexes {
    init_state axiom forall bytes32 x. rolesGhostIndexes[x] == 0;
}
// ghost field for the length of the values array (stored in offset 0)
ghost uint256 rolesGhostLength {
    // assumption: it's infeasible to grow the list to these many elements.
    axiom rolesGhostLength < 0xffffffffffffffffffffffffffffffff;
}

// roleMembers
ghost mapping(bytes32 => mapping(mathint => bytes32)) roleMembersGhostValues {
    init_state axiom forall bytes32 x. forall mathint y. roleMembersGhostValues[x][y] == to_bytes32(0);
}
// ghost field for the indexes map
ghost mapping(bytes32 => mapping(bytes32 => uint256)) roleMembersGhostIndexes {
    init_state axiom forall bytes32 x. forall bytes32 y. roleMembersGhostIndexes[x][y] == 0;
}
// ghost field for the length of the values array (stored in offset 0)
ghost mapping(bytes32 => uint256) roleMembersGhostLength {
    // assumption: it's infeasible to grow the list to these many elements.
    axiom forall bytes32 x. roleMembersGhostLength[x] < 0xffffffffffffffffffffffffffffffff;
}


// HOOKS
// Store hook to synchronize rolesGhostLength with the length of the roles._inner._values array.
// We need to use (offset 0) here, as there is no keyword yet to access the length.

// roles
hook Sstore currentContract.roles.(offset 0) uint256 newLength STORAGE {
    rolesGhostLength = newLength;
}
// Store hook to synchronize rolesGhostValues array with roles._inner._values.
hook Sstore currentContract.roles._inner._values[INDEX uint256 index] bytes32 newValue STORAGE {
    rolesGhostValues[index] = newValue;
}
// Store hook to synchronize rolesGhostIndexes array with roles._inner._indexes.
hook Sstore currentContract.roles._inner._indexes[KEY bytes32 value] uint256 newIndex STORAGE {
    rolesGhostIndexes[value] = newIndex;
}


// roleMembers
hook Sstore currentContract.roleMembers[KEY bytes32 roleKey].(offset 0) uint256 newLength STORAGE {
    roleMembersGhostLength[roleKey] = newLength;
}
// Store hook to synchronize roleMembersGhostValues array with roleMembers[roleKey]._inner._values.
hook Sstore currentContract.roleMembers[KEY bytes32 roleKey]._inner._values[INDEX uint256 index] bytes32 newValue STORAGE {
    roleMembersGhostValues[roleKey][index] = newValue;
}
// Store hook to synchronize roleMembersGhostIndexes array with roleMembers[roleKey]._inner._indexes.
hook Sstore currentContract.roleMembers[KEY bytes32 roleKey]._inner._indexes[KEY bytes32 value] uint256 newIndex STORAGE {
    roleMembersGhostIndexes[roleKey][value] = newIndex;
}

// The load hooks can use require to ensure that the ghost field has the same information as the storage.
// The require is sound, since the store hooks ensure the contents are always the same.  However we cannot
// prove that with invariants, since this would require the invariant to read the storage for all elements
// and neither storage access nor function calls are allowed in quantifiers.
//
// By following this simple pattern it is ensured that the ghost state and the storage are always the same
// and that the solver can use this knowledge in the proofs.

// Load hook to synchronize rolesGhostLength with the length of the roles._inner._values array.
// Again we use (offset 0) here, as there is no keyword yet to access the length.

// roles
hook Sload uint256 length currentContract.roles.(offset 0) STORAGE {
    require rolesGhostLength == length;
}
hook Sload bytes32 value currentContract.roles._inner._values[INDEX uint256 index] STORAGE {
    require rolesGhostValues[index] == value;
}
hook Sload uint256 index currentContract.roles._inner._indexes[KEY bytes32 value] STORAGE {
    require rolesGhostIndexes[value] == index;
}


// roleMembers
hook Sload uint256 length currentContract.roleMembers[KEY bytes32 roleKey].(offset 0) STORAGE {
    require roleMembersGhostLength[roleKey] == length;
}
hook Sload bytes32 value currentContract.roleMembers[KEY bytes32 roleKey]._inner._values[INDEX uint256 index] STORAGE {
    require roleMembersGhostValues[roleKey][index] == value;
}
hook Sload uint256 index currentContract.roleMembers[KEY bytes32 roleKey]._inner._indexes[KEY bytes32 value] STORAGE {
    require roleMembersGhostIndexes[roleKey][value] == index;
}

// INVARIANTS

//  This is the main invariant stating that the indexes and values always match:
//        values[indexes[v] - 1] = v for all values v in the set
//    and indexes[values[i]] = i+1 for all valid indexes i.

invariant rolesEnumerableSetInvariant()
    (forall uint256 index. 0 <= index && index < rolesGhostLength => to_mathint(rolesGhostIndexes[rolesGhostValues[index]]) == index + 1)
    && (forall bytes32 value. rolesGhostIndexes[value] == 0 ||
         (rolesGhostValues[rolesGhostIndexes[value] - 1] == value && rolesGhostIndexes[value] >= 1 && rolesGhostIndexes[value] <= rolesGhostLength));


invariant roleMembersEnumerableSetInvariant()
    (forall bytes32 roleKey.
      (forall uint256 index. 0 <= index && index < roleMembersGhostLength[roleKey] => to_mathint(roleMembersGhostIndexes[roleKey][roleMembersGhostValues[roleKey][index]]) == index + 1)
      && (forall bytes32 value. roleMembersGhostIndexes[roleKey][value] == 0 ||
          (roleMembersGhostValues[roleKey][roleMembersGhostIndexes[roleKey][value] - 1] == value && roleMembersGhostIndexes[roleKey][value] >= 1 && roleMembersGhostIndexes[roleKey][value] <= roleMembersGhostLength[roleKey]))
    )
    {
      preserved with (env e1) {
        require Role.ROLE_ADMIN(e1) != to_bytes32(0);
      }
    }
