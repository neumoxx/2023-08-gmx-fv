using RoleStore as ROLE_STORE;

methods {
    // DataStore
    function _.getUint(bytes32) external => DISPATCHER(true);
    function _.getAddress(bytes32) external => DISPATCHER(true);
    function _.getBytes32(bytes32) external => DISPATCHER(true);
    // RoleStore
    function _.hasRole(address,bytes32) external => DISPATCHER(true);
    // OracleStore
    function _.getSigner(uint256) external => DISPATCHER(true);
    // PriceFeed
    function _.latestRoundData() external => DISPATCHER(true);
    /// Chain
    function _.arbBlockNumber() external => ghostBlockNumber() expect uint256 ALL;
    function _.arbBlockHash(uint256 blockNumber) external => ghostBlockHash(blockNumber) expect bytes32 ALL;
    /// Oracle summaries
    function Oracle._getSalt() internal returns bytes32 => mySalt();

    /// Getters:
    function OracleHarness.primaryPrices(address) external returns (uint256,uint256);
    function OracleHarness.secondaryPrices(address) external returns (uint256,uint256);
    function OracleHarness.customPrices(address) external returns (uint256,uint256);
    function OracleHarness.getSignerByInfo(uint256, uint256) external returns (address);
}


// DEFINITIONS

/// @notice Functions defined in harness contract
definition notHarnessCall(method f) returns bool =
    (f.selector != sig:setPrices(address, address,OracleUtils.SetPricesParams).selector
    && f.selector != sig:getStablePrice(address, address).selector
    && f.selector != sig:getPriceFeedMultiplier(address, address).selector
    && f.selector != sig:getSignerByInfo(uint256, uint256).selector
    && f.selector != sig:validateSignerHarness(bytes32, bytes, address).selector);


// FUNCTIONS

function ghostMedian(uint256[] array) returns uint256 {
    uint256 med;
    uint256 len = array.length;
    require med >= array[0] && med <= array[require_uint256(len-1)];
    return med;
}


// RULES

rule sanity_satisfy(method f) {
    env e;
    calldataarg args;
    f(e, args);
    satisfy true;
}

rule validateSignerConsistency() {
    env e1; env e2;
    require e1.msg.value == e2.msg.value;

    bytes32 salt1;
    bytes32 salt2;
    address signer1;
    address signer2;
    bytes signature;

    validateSignerHarness(e1, salt1, signature, signer1);
    validateSignerHarness@withrevert(e2, salt2, signature, signer2);

    assert (salt1 == salt2 && signer1 == signer2) => !lastReverted,
        "Revert characteristics of validateSigner are not consistent";
}


// GHOSTS

ghost mySalt() returns bytes32;

ghost ghostBlockNumber() returns uint256 {
    axiom ghostBlockNumber() !=0;
}

ghost ghostBlockHash(uint256) returns bytes32 {
    axiom forall uint256 num1. forall uint256 num2.
        num1 != num2 => ghostBlockHash(num1) != ghostBlockHash(num2);
}

// tokensWithPrices

// ghost field for the values array
ghost mapping(mathint => bytes32) tokensWithPricesGhostValues {
    init_state axiom forall mathint x. tokensWithPricesGhostValues[x] == to_bytes32(0);
}
// ghost field for the indexes map
ghost mapping(bytes32 => uint256) tokensWithPricesGhostIndexes {
    init_state axiom forall bytes32 x. tokensWithPricesGhostIndexes[x] == 0;
}
// ghost field for the length of the values array (stored in offset 0)
ghost uint256 tokensWithPricesGhostLength {
    // assumption: it's infeasible to grow the list to these many elements.
    axiom tokensWithPricesGhostLength < 0xffffffffffffffffffffffffffffffff;
}




// HOOKS
// Store hook to synchronize tokensWithPricesGhostLength with the length of the tokensWithPrices._inner._values array.
// We need to use (offset 0) here, as there is no keyword yet to access the length.

// tokensWithPrices
hook Sstore currentContract.tokensWithPrices.(offset 0) uint256 newLength STORAGE {
    tokensWithPricesGhostLength = newLength;
}
// Store hook to synchronize tokensWithPricesGhostValues array with tokensWithPrices._inner._values.
hook Sstore currentContract.tokensWithPrices._inner._values[INDEX uint256 index] bytes32 newValue STORAGE {
    tokensWithPricesGhostValues[index] = newValue;
}
// Store hook to synchronize tokensWithPricesGhostIndexes array with tokensWithPrices._inner._indexes.
hook Sstore currentContract.tokensWithPrices._inner._indexes[KEY bytes32 value] uint256 newIndex STORAGE {
    tokensWithPricesGhostIndexes[value] = newIndex;
}

hook Sload uint256 length currentContract.tokensWithPrices.(offset 0) STORAGE {
    require tokensWithPricesGhostLength == length;
}
hook Sload bytes32 value currentContract.tokensWithPrices._inner._values[INDEX uint256 index] STORAGE {
    require tokensWithPricesGhostValues[index] == value;
}
hook Sload uint256 index currentContract.tokensWithPrices._inner._indexes[KEY bytes32 value] STORAGE {
    require tokensWithPricesGhostIndexes[value] == index;
}


// INVARIANTS

//  This is the main invariant stating that the indexes and values always match:
//        values[indexes[v] - 1] = v for all values v in the set
//    and indexes[values[i]] = i+1 for all valid indexes i.

invariant tokensWithPricesEnumerableSetInvariant()
    (forall uint256 index. 0 <= index && index < tokensWithPricesGhostLength => to_mathint(tokensWithPricesGhostIndexes[tokensWithPricesGhostValues[index]]) == index + 1)
    && (forall bytes32 value. tokensWithPricesGhostIndexes[value] == 0 ||
         (tokensWithPricesGhostValues[tokensWithPricesGhostIndexes[value] - 1] == value && tokensWithPricesGhostIndexes[value] >= 1 && tokensWithPricesGhostIndexes[value] <= tokensWithPricesGhostLength));

