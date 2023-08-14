using RoleStore as ROLE_STORE;

methods {

    function getUint(bytes32) external returns (uint256) envfree;
    function setUint(bytes32, uint256) external returns (uint256);
    function removeUint(bytes32) external;
    function applyDeltaToUint(bytes32, int256, string) external returns (uint256);
    function applyDeltaToUint(bytes32, uint256) external returns (uint256);
    function applyBoundedDeltaToUint(bytes32, int256) external returns (uint256);
    function incrementUint(bytes32, uint256) external returns (uint256);
    function decrementUint(bytes32, uint256) external returns (uint256);
    function getInt(bytes32) external returns (int256) envfree;
    function setInt(bytes32, int256) external returns (int256);
    function removeInt(bytes32) external;
    function applyDeltaToInt(bytes32, int256) external returns (int256);
    function incrementInt(bytes32, int256) external returns (int256);
    function decrementInt(bytes32, int256) external returns (int256);
    function getAddress(bytes32) external returns (address) envfree;
    function setAddress(bytes32, address) external returns (address);
    function removeAddress(bytes32) external;
    function getBool(bytes32) external returns (bool) envfree;
    function setBool(bytes32, bool) external returns (bool);
    function removeBool(bytes32) external;
    function getString(bytes32) external returns (string) envfree;
    function setString(bytes32, string) external returns (string);
    function removeString(bytes32) external;
    function getBytes32(bytes32) external returns (bytes32) envfree;
    function setBytes32(bytes32, bytes32) external returns (bytes32);
    function removeBytes32(bytes32) external;
    function getUintArray(bytes32) external returns (uint256[]) envfree;
    function setUintArray(bytes32, uint256[]) external;
    function removeUintArray(bytes32) external;
    function getIntArray(bytes32) external returns (int256[]) envfree;
    function setIntArray(bytes32, int256[]) external;
    function removeIntArray(bytes32) external;
    function getAddressArray(bytes32) external returns (address[]) envfree;
    function setAddressArray(bytes32, address[]) external;
    function removeAddressArray(bytes32) external;
    function getBoolArray(bytes32) external returns (bool[]) envfree;
    function setBoolArray(bytes32, bool[]) external;
    function removeBoolArray(bytes32) external;
    function getStringArray(bytes32) external returns (string[]) envfree;
    function removeStringArray(bytes32) external;
    function getBytes32Array(bytes32) external returns (bytes32[]) envfree;
    function setBytes32Array(bytes32, bytes32[]) external;
    function removeBytes32Array(bytes32) external;

    function containsBytes32(bytes32, bytes32) external returns (bool) envfree;
    function getBytes32Count(bytes32) external returns (uint256) envfree;
    function getBytes32ValuesAt(bytes32, uint256, uint256) external returns (bytes32[]) envfree;
    function addBytes32(bytes32, bytes32) external;
    function removeBytes32(bytes32, bytes32) external;
    function containsAddress(bytes32, address) external returns (bool) envfree;
    function getAddressCount(bytes32) external returns (uint256) envfree;
    function getAddressValuesAt(bytes32, uint256, uint256) external returns (address[]) envfree;
    function addAddress(bytes32, address) external;
    function removeAddress(bytes32, address) external;
    function containsUint(bytes32, uint256) external returns (bool) envfree;
    function getUintCount(bytes32) external returns (uint256) envfree;
    function getUintValuesAt(bytes32, uint256, uint256) external returns (uint256[]) envfree;
    function addUint(bytes32, uint256) external;
    function removeUint(bytes32, uint256) external;

    // harness
    function CONTROLLER() external returns (bytes32) envfree;
    function maxInt256() external returns (int256) envfree;
    function minInt256() external returns (int256) envfree;
    function stringLength(string) external returns (uint256) envfree;
    function stringsEqual(string, string) external returns (bool) envfree;
    function uintArraysEqual(uint[], uint[]) external returns (bool) envfree;
    function intArraysEqual(int[], int[]) external returns (bool) envfree;
    function addressArraysEqual(address[], address[]) external returns (bool) envfree;
    function boolArraysEqual(bool[], bool[]) external returns (bool) envfree;
    function stringArraysEqual(string[], string[]) external returns (bool) envfree;
    function stringArraysEqual(string[], bytes32) external returns (bool) envfree;
    function bytes32ArraysEqual(bytes32[], bytes32[]) external returns (bool) envfree;

    // RoleStore.sol
    function _.hasRole(address, bytes32) external => DISPATCHER(true);
}


// DEFINITION

/// @notice Functions defined in harness contract
definition notHarnessCall(method f) returns bool =
    (f.selector != sig:maxInt256().selector
    && f.selector != sig:minInt256().selector
    && f.selector != sig:stringLength(string).selector
    && f.selector != sig:stringsEqual(string, string).selector
    && f.selector != sig:uintArraysEqual(uint[], uint[]).selector
    && f.selector != sig:intArraysEqual(int[], int[]).selector
    && f.selector != sig:addressArraysEqual(address[], address[]).selector
    && f.selector != sig:boolArraysEqual(bool[], bool[]).selector
    && f.selector != sig:stringArraysEqual(string[], string[]).selector
    && f.selector != sig:stringArraysEqual(string[], bytes32).selector
    && f.selector != sig:bytes32ArraysEqual(bytes32[], bytes32[]).selector);


// RULES

rule uintConsistencyChecks(env e) {

    bytes32 key;
    uint256 value;
    int256 intValue;
    string errorMessage = "error";

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setUint & getUint
    setUint@withrevert(e, key, value);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => value == getUint(key);

    // removeUint
    removeUint@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => 0 == getUint(key);

    // applyDeltaToUint (int)
    uint256 cachedValue1 = getUint(key);
    applyDeltaToUint@withrevert(e, key, intValue, errorMessage);
    assert lastReverted <=> (
      e.msg.value > 0 ||
      !isController ||
      (intValue < 0 && -1*intValue > to_mathint(cachedValue1))
    );
    uint256 res1 = require_uint256(cachedValue1 + intValue);
    assert !lastReverted => getUint(key) == res1;

    // applyDeltaToUint (uint)
    uint256 cachedValue2 = getUint(key);
    applyDeltaToUint@withrevert(e, key, value);
    assert lastReverted <=> (
      e.msg.value > 0 ||
      !isController ||
      (cachedValue2 + value > to_mathint(max_uint256))
    );
    uint256 res2 = require_uint256(cachedValue2 + value);
    assert !lastReverted => getUint(key) == res2;

    // applyBoundedDeltaToUint
    uint256 cachedValue3 = getUint(key);
    applyBoundedDeltaToUint@withrevert(e, key, intValue);
    uint256 res3 = require_uint256(cachedValue3 + intValue);
    assert lastReverted <=> (
      e.msg.value > 0 ||
      !isController
    );
    assert !lastReverted => (
      !(intValue < 0 && -1*intValue > to_mathint(cachedValue3)) => getUint(key) == res3 &&
      (intValue < 0 && -1*intValue > to_mathint(cachedValue3)) => getUint(key) == 0
    );

    // incrementUint
    uint256 cachedValue4 = getUint(key);
    incrementUint@withrevert(e, key, value);
    assert lastReverted <=> (
      e.msg.value > 0 ||
      !isController ||
      (cachedValue4 + value > to_mathint(max_uint256))
    );
    uint256 res4 = require_uint256(cachedValue4 + value);
    assert !lastReverted => getUint(key) == res4;

    // decrementUint
    uint256 cachedValue5 = getUint(key);
    decrementUint@withrevert(e, key, value);
    assert lastReverted <=> (
      e.msg.value > 0 ||
      !isController ||
      (cachedValue5 - value < to_mathint(0))
    );
    uint256 res5 = require_uint256(cachedValue5 - value);
    assert !lastReverted => getUint(key) == res5;

}

rule intConsistencyChecks(env e) {

    int256 max_int256 = maxInt256();
    int256 min_int256 = minInt256();

    bytes32 key;
    int256 value;

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setInt & getInt
    setInt@withrevert(e, key, value);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => value == getInt(key);

    // removeInt
    removeInt@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => 0 == getInt(key);

    // applyDeltaToInt
    int256 cachedValue1 = getInt(key);
    applyDeltaToInt@withrevert(e, key, value);
    assert lastReverted <=> (
      e.msg.value > 0 ||
      !isController ||
      (value + cachedValue1 > to_mathint(max_int256))
    );
    int256 res1 = require_int256(cachedValue1 + value);
    assert !lastReverted => getInt(key) == res1;

    // incrementInt
    int256 cachedValue2 = getInt(key);
    incrementInt@withrevert(e, key, value);
    assert lastReverted <=> (
      e.msg.value > 0 ||
      !isController ||
      (cachedValue2 + value > to_mathint(max_int256)) ||
      (cachedValue2 + value < to_mathint(min_int256))
    );
    int256 res2 = require_int256(cachedValue2 + value);
    assert !lastReverted => getInt(key) == res2;

    // decrementInt
    int256 cachedValue3 = getInt(key);
    decrementInt@withrevert(e, key, value);
    assert lastReverted <=> (
      e.msg.value > 0 ||
      !isController ||
      (cachedValue2 + value > to_mathint(max_int256)) ||
      (cachedValue2 - value < to_mathint(min_int256))
    );
    int256 res3 = require_int256(cachedValue3 - value);
    assert !lastReverted => getInt(key) == res3;

}

rule addressConsistencyChecks(env e) {

    bytes32 key;
    address value;

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setAddress & getAddress
    setAddress@withrevert(e, key, value);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => value == getAddress(key);

    // removeAddress
    removeAddress@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => 0 == getAddress(key);

}

rule boolConsistencyChecks(env e) {

    bytes32 key;
    bool value;

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setBool & getBool
    setBool@withrevert(e, key, value);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => value == getBool(key);

    // removeBool
    removeBool@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => false == getBool(key);

}

rule stringConsistencyChecks(env e) {

    bytes32 key;
    string value;

    require stringLength(value) < 10; // make rule less computationally intensive

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setString & getString
    setString@withrevert(e, key, value);
    assert (e.msg.value > 0 || !isController) => lastReverted;
    assert !lastReverted => stringsEqual(value, getString(key));

    // removeString
    removeString@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => stringLength(getString(key)) == 0;

}

rule bytes32ConsistencyChecks(env e) {

    bytes32 key;
    bytes32 value;

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setBytes32 & getBytes32
    setBytes32@withrevert(e, key, value);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => value == getBytes32(key);

    // removeBytes32
    removeBytes32@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => to_bytes32(0) == getBytes32(key);

}

rule uintArrayConsistencyChecks(env e) {

    bytes32 key;
    uint256[] value;
    uint256[] emptyArray;

    require emptyArray.length == 0;
    require value.length < 10; // make rule less computationally intensive

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setUintArray & getUintArray
    setUintArray@withrevert(e, key, value);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => uintArraysEqual(value, getUintArray(key));

    // removeStringUintArray
    removeUintArray@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => uintArraysEqual(emptyArray, getUintArray(key));

}

rule intArrayConsistencyChecks(env e) {

    bytes32 key;
    int256[] value;
    int256[] emptyArray;

    require emptyArray.length == 0;
    require value.length < 10; // make rule less computationally intensive

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setIntArray & getIntArray
    setIntArray@withrevert(e, key, value);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => intArraysEqual(value, getIntArray(key));

    // removeIntArray
    removeIntArray@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => intArraysEqual(emptyArray, getIntArray(key));

}

rule addressArrayConsistencyChecks(env e) {

    bytes32 key;
    address[] value;
    address[] emptyArray;

    require emptyArray.length == 0;
    require value.length < 10; // make rule less computationally intensive

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setAddressArray & getAddressArray
    setAddressArray@withrevert(e, key, value);
    assert (e.msg.value > 0 || !isController) => lastReverted;
    assert !lastReverted => addressArraysEqual(value, getAddressArray(key));

    // removeAddressArray
    removeAddressArray@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => addressArraysEqual(emptyArray, getAddressArray(key));

}

rule boolArrayConsistencyChecks(env e) {

    bytes32 key;
    bool[] value;
    bool[] emptyArray;

    require emptyArray.length == 0;
    require value.length < 10; // make rule less computationally intensive

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setBoolArray & getBoolArray
    setBoolArray@withrevert(e, key, value);
    assert (e.msg.value > 0 || !isController) => lastReverted;
    assert !lastReverted => boolArraysEqual(value, getBoolArray(key));

    // removeBoolArray
    removeBoolArray@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => boolArraysEqual(emptyArray, getBoolArray(key));

}

rule stringArrayConsistencyChecks(env e) {

    bytes32 key;
    string[] value;
    string[] emptyArray;

    require emptyArray.length == 0;
    require value.length < 10; // make rule less computationally intensive

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // getStringArray && removeStringArray
    removeStringArray@withrevert(e, key);
    assert (e.msg.value > 0 || !isController) => lastReverted;
    assert !lastReverted => stringArraysEqual(emptyArray, key);

}

rule bytes32ArrayConsistencyChecks(env e) {

    bytes32 key;
    bytes32[] value;
    bytes32[] emptyArray;

    require emptyArray.length == 0;
    require value.length < 10; // make rule less computationally intensive

    bool isController = ROLE_STORE.hasRole(e, e.msg.sender, CONTROLLER());

    // setBytes32Array & getBytes32Array
    setBytes32Array@withrevert(e, key, value);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => bytes32ArraysEqual(value, getBytes32Array(key));

    // removeBytes32Array
    removeBytes32Array@withrevert(e, key);
    assert lastReverted <=> (e.msg.value > 0 || !isController);
    assert !lastReverted => bytes32ArraysEqual(emptyArray, getBytes32Array(key));

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

// bytes32Sets

// ghost field for the values array
ghost mapping(bytes32 => mapping(mathint => bytes32)) bytes32SetsGhostValues {
    init_state axiom forall bytes32 x. forall mathint y. bytes32SetsGhostValues[x][y] == to_bytes32(0);
}
// ghost field for the indexes map
ghost mapping(bytes32 => mapping(bytes32 => uint256)) bytes32SetsGhostIndexes {
    init_state axiom forall bytes32 x. forall bytes32 y.  bytes32SetsGhostIndexes[x][y] == 0;
}
// ghost field for the length of the values array (stored in offset 0)
ghost mapping(bytes32 => uint256) bytes32SetsGhostLength {
    // assumption: it's infeasible to grow the list to these many elements.
    axiom forall bytes32 x. bytes32SetsGhostLength[x] < 0xffffffffffffffffffffffffffffffff;
}


// HOOKS
// Store hook to synchronize bytes32SetsGhostLength with the length of the bytes32Sets._inner._values array.
// We need to use (offset 0) here, as there is no keyword yet to access the length.

// bytes32Sets

hook Sstore currentContract.bytes32Sets[KEY bytes32 setKey].(offset 0) uint256 newLength STORAGE {
    bytes32SetsGhostLength[setKey] = newLength;
}
// Store hook to synchronize bytes32SetsGhostValues array with bytes32Sets[KEY bytes32 setKey]._inner._values.
hook Sstore currentContract.bytes32Sets[KEY bytes32 setKey]._inner._values[INDEX uint256 index] bytes32 newValue STORAGE {
    bytes32SetsGhostValues[setKey][index] = newValue;
}
// Store hook to synchronize bytes32SetsGhostIndexes array with bytes32Sets[KEY bytes32 setKey]._inner._indexes.
hook Sstore currentContract.bytes32Sets[KEY bytes32 setKey]._inner._indexes[KEY bytes32 value] uint256 newIndex STORAGE {
    bytes32SetsGhostIndexes[setKey][value] = newIndex;
}

hook Sload uint256 length currentContract.bytes32Sets[KEY bytes32 setKey].(offset 0) STORAGE {
    require bytes32SetsGhostLength[setKey] == length;
}
hook Sload bytes32 value currentContract.bytes32Sets[KEY bytes32 setKey]._inner._values[INDEX uint256 index] STORAGE {
    require bytes32SetsGhostValues[setKey][index] == value;
}
hook Sload uint256 index currentContract.bytes32Sets[KEY bytes32 setKey]._inner._indexes[KEY bytes32 value] STORAGE {
    require bytes32SetsGhostIndexes[setKey][value] == index;
}



// INVARIANTS

//  This is the main invariant stating that the indexes and values always match:
//        values[indexes[v] - 1] = v for all values v in the set
//    and indexes[values[i]] = i+1 for all valid indexes i.

invariant bytes32SetsEnumerableSetInvariant()
    (forall bytes32 setKey. (forall uint256 index. 0 <= index && index < bytes32SetsGhostLength[setKey] => to_mathint(bytes32SetsGhostIndexes[setKey][bytes32SetsGhostValues[setKey][index]]) == index + 1)
      && (forall bytes32 value. bytes32SetsGhostIndexes[setKey][value] == 0 ||
          (bytes32SetsGhostValues[setKey][bytes32SetsGhostIndexes[setKey][value] - 1] == value && bytes32SetsGhostIndexes[setKey][value] >= 1 && bytes32SetsGhostIndexes[setKey][value] <= bytes32SetsGhostLength[setKey]))
    );
