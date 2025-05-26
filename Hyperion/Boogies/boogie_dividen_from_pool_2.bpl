
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

datatype Vec<T> {
    Vec(v: [int]T, l: int)
}

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := v->l;
    Vec(v->v[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v->v[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    v->l
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    v->l == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := v->l - 1;
    Vec(v->v[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := v->l - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v->v[j] else v->v[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := v1->l, v1->v, v2->l, v2->v;
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := v->l;
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v->v[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v->v[i := elem], v->l)
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(m[i := m[j]][j := m[i]], v->l))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := v->l;
    (exists i: int :: InRangeVec(v, i) && v->v[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

datatype Multiset<T> {
    Multiset(v: [T]int, l: int)
}

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    s->l
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := s->l;
    (var cnt := s->v[v];
    Multiset(s->v[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := s1->l;
    (var len2 := s2->l;
    Multiset((lambda v:T :: s1->v[v]-s2->v[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (s->l == 0) &&
    (forall v: T :: s->v[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (s1->l <= s2->l) &&
    (forall v: T :: s1->v[v] <= s2->v[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    s->v[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
datatype Table <K, V> {
    Table(v: [K]V, e: [K]bool, l: int)
}

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    t->v[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    t->l
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    t->e[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(t->v[k := v], t->e, t->l)
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(t->v[k := v], t->e[k := true], t->l + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(t->v, t->e[k := false], t->l - 1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.
// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

// ==================================================================================
// Native object::exists_at

// ==================================================================================
// Intrinsic implementation of aggregator and aggregator factory

datatype $1_aggregator_Aggregator {
    $1_aggregator_Aggregator($handle: int, $key: int, $limit: int, $val: int)
}
function {:inline} $Update'$1_aggregator_Aggregator'_handle(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(x, s->$key, s->$limit, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_key(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, x, s->$limit, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_limit(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, s->$key, x, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_val(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, s->$key, s->$limit, x)
}
function $IsValid'$1_aggregator_Aggregator'(s: $1_aggregator_Aggregator): bool {
    $IsValid'address'(s->$handle)
      && $IsValid'address'(s->$key)
      && $IsValid'u128'(s->$limit)
      && $IsValid'u128'(s->$val)
}
function {:inline} $IsEqual'$1_aggregator_Aggregator'(s1: $1_aggregator_Aggregator, s2: $1_aggregator_Aggregator): bool {
    s1 == s2
}
function {:inline} $1_aggregator_spec_get_limit(s: $1_aggregator_Aggregator): int {
    s->$limit
}
function {:inline} $1_aggregator_limit(s: $1_aggregator_Aggregator): int {
    s->$limit
}
procedure {:inline 1} $1_aggregator_limit(s: $1_aggregator_Aggregator) returns (res: int) {
    res := s->$limit;
    return;
}
function {:inline} $1_aggregator_spec_get_handle(s: $1_aggregator_Aggregator): int {
    s->$handle
}
function {:inline} $1_aggregator_spec_get_key(s: $1_aggregator_Aggregator): int {
    s->$key
}
function {:inline} $1_aggregator_spec_get_val(s: $1_aggregator_Aggregator): int {
    s->$val
}

function $1_aggregator_spec_read(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_spec_aggregator_set_val(agg: $1_aggregator_Aggregator, val: int): $1_aggregator_Aggregator {
    $Update'$1_aggregator_Aggregator'_val(agg, val)
}

function $1_aggregator_spec_aggregator_get_val(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_factory_spec_new_aggregator(limit: int) : $1_aggregator_Aggregator;

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
    (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_get_limit(agg) == limit));

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
     (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_aggregator_get_val(agg) == 0));

// ==================================================================================
// Native for function_info

procedure $1_function_info_is_identifier(s: Vec int) returns (res: bool);



// Uninterpreted function for all types

function $Arbitrary_value_of'#0'(): #0;

function $Arbitrary_value_of'$1_big_vector_BigVector'address''(): $1_big_vector_BigVector'address';

function $Arbitrary_value_of'$1_fungible_asset_BurnRef'(): $1_fungible_asset_BurnRef;

function $Arbitrary_value_of'$1_fungible_asset_FungibleAsset'(): $1_fungible_asset_FungibleAsset;

function $Arbitrary_value_of'$1_fungible_asset_MintRef'(): $1_fungible_asset_MintRef;

function $Arbitrary_value_of'$1_fungible_asset_TransferRef'(): $1_fungible_asset_TransferRef;

function $Arbitrary_value_of'$1_object_ExtendRef'(): $1_object_ExtendRef;

function $Arbitrary_value_of'$1_object_Object'$1_fungible_asset_FungibleStore''(): $1_object_Object'$1_fungible_asset_FungibleStore';

function $Arbitrary_value_of'$1_object_Object'$1_fungible_asset_Metadata''(): $1_object_Object'$1_fungible_asset_Metadata';

function $Arbitrary_value_of'$1_option_Option'$1_big_vector_BigVector'address'''(): $1_option_Option'$1_big_vector_BigVector'address'';

function $Arbitrary_value_of'$1_option_Option'$1_fungible_asset_FungibleAsset''(): $1_option_Option'$1_fungible_asset_FungibleAsset';

function $Arbitrary_value_of'$1_option_Option'u64''(): $1_option_Option'u64';

function $Arbitrary_value_of'$1_permissioned_signer_GrantedPermissionHandles'(): $1_permissioned_signer_GrantedPermissionHandles;

function $Arbitrary_value_of'$1_smart_vector_SmartVector'address''(): $1_smart_vector_SmartVector'address';

function $Arbitrary_value_of'$1_string_String'(): $1_string_String;

function $Arbitrary_value_of'$aa_i128_I128'(): $aa_i128_I128;

function $Arbitrary_value_of'$aa_i32_I32'(): $aa_i32_I32;

function $Arbitrary_value_of'$aa_lp_LPTokenRefs'(): $aa_lp_LPTokenRefs;

function $Arbitrary_value_of'$aa_pool_v3_LiquidityPoolV3'(): $aa_pool_v3_LiquidityPoolV3;

function $Arbitrary_value_of'$aa_pool_v3_ProtocolFees'(): $aa_pool_v3_ProtocolFees;

function $Arbitrary_value_of'$aa_position_blacklist_PositionBlackList'(): $aa_position_blacklist_PositionBlackList;

function $Arbitrary_value_of'$aa_rewarder_RewarderManager'(): $aa_rewarder_RewarderManager;

function $Arbitrary_value_of'$aa_tick_bitmap_BitMap'(): $aa_tick_bitmap_BitMap;

function $Arbitrary_value_of'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(): Table int ($aa_tick_TickInfo);

function $Arbitrary_value_of'$1_table_with_length_TableWithLength'u64_vec'#0'''(): Table int (Vec (#0));

function $Arbitrary_value_of'$1_table_with_length_TableWithLength'u64_vec'address'''(): Table int (Vec (int));

function $Arbitrary_value_of'$1_table_Table'$aa_i32_I32_u256''(): Table int (int);

function $Arbitrary_value_of'vec'#0''(): Vec (#0);

function $Arbitrary_value_of'vec'$1_big_vector_BigVector'address'''(): Vec ($1_big_vector_BigVector'address');

function $Arbitrary_value_of'vec'$1_fungible_asset_FungibleAsset''(): Vec ($1_fungible_asset_FungibleAsset);

function $Arbitrary_value_of'vec'$aa_rewarder_Rewarder''(): Vec ($aa_rewarder_Rewarder);

function $Arbitrary_value_of'vec'address''(): Vec (int);

function $Arbitrary_value_of'vec'u128''(): Vec (int);

function $Arbitrary_value_of'vec'u64''(): Vec (int);

function $Arbitrary_value_of'vec'u8''(): Vec (int);

function $Arbitrary_value_of'bool'(): bool;

function $Arbitrary_value_of'address'(): int;

function $Arbitrary_value_of'u128'(): int;

function $Arbitrary_value_of'u256'(): int;

function $Arbitrary_value_of'u32'(): int;

function $Arbitrary_value_of'u64'(): int;

function $Arbitrary_value_of'u8'(): int;

function $Arbitrary_value_of'$1_table_Table'$aa_i32_I32_bv256''(): Table int (bv256);

function $Arbitrary_value_of'vec'bv128''(): Vec (bv128);

function $Arbitrary_value_of'vec'bv64''(): Vec (bv64);

function $Arbitrary_value_of'vec'bv8''(): Vec (bv8);

function $Arbitrary_value_of'bv128'(): bv128;

function $Arbitrary_value_of'bv256'(): bv256;

function $Arbitrary_value_of'bv32'(): bv32;

function $Arbitrary_value_of'bv64'(): bv64;

function $Arbitrary_value_of'bv8'(): bv8;



// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U16: int;
axiom $MAX_U16 == 65535;
const $MAX_U32: int;
axiom $MAX_U32 == 4294967295;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;
const $MAX_U256: int;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

// Templates for bitvector operations

function {:bvbuiltin "bvand"} $And'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvor"} $Or'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvxor"} $Xor'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvadd"} $Add'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsub"} $Sub'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvmul"} $Mul'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvudiv"} $Div'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvurem"} $Mod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvshl"} $Shl'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvlshr"} $Shr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} $Lt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv8'(bv8,bv8) returns(bool);

procedure {:inline 1} $AddBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Add'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $AddBv8_unchecked(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $SubBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv8'(src1, src2);
}

procedure {:inline 1} $MulBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Mul'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv8'(src1, src2);
}

procedure {:inline 1} $DivBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv8'(src1, src2);
}

procedure {:inline 1} $ModBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv8'(src1, src2);
}

procedure {:inline 1} $AndBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $And'Bv8'(src1,src2);
}

procedure {:inline 1} $OrBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Or'Bv8'(src1,src2);
}

procedure {:inline 1} $XorBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Xor'Bv8'(src1,src2);
}

procedure {:inline 1} $LtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Lt'Bv8'(src1,src2);
}

procedure {:inline 1} $LeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Le'Bv8'(src1,src2);
}

procedure {:inline 1} $GtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Gt'Bv8'(src1,src2);
}

procedure {:inline 1} $GeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Ge'Bv8'(src1,src2);
}

function $IsValid'bv8'(v: bv8): bool {
  $Ge'Bv8'(v,0bv8) && $Le'Bv8'(v,255bv8)
}

function {:inline} $IsEqual'bv8'(x: bv8, y: bv8): bool {
    x == y
}

procedure {:inline 1} $int2bv8(src: int) returns (dst: bv8)
{
    if (src > 255) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.8(src);
}

procedure {:inline 1} $bv2int8(src: bv8) returns (dst: int)
{
    dst := $bv2int.8(src);
}

function {:builtin "(_ int2bv 8)"} $int2bv.8(i: int) returns (bv8);
function {:builtin "bv2nat"} $bv2int.8(i: bv8) returns (int);

function {:bvbuiltin "bvand"} $And'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvor"} $Or'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvxor"} $Xor'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvadd"} $Add'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsub"} $Sub'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvmul"} $Mul'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvudiv"} $Div'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvurem"} $Mod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvshl"} $Shl'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvlshr"} $Shr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvult"} $Lt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv16'(bv16,bv16) returns(bool);

procedure {:inline 1} $AddBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Add'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $AddBv16_unchecked(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $SubBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv16'(src1, src2);
}

procedure {:inline 1} $MulBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Mul'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv16'(src1, src2);
}

procedure {:inline 1} $DivBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv16'(src1, src2);
}

procedure {:inline 1} $ModBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv16'(src1, src2);
}

procedure {:inline 1} $AndBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $And'Bv16'(src1,src2);
}

procedure {:inline 1} $OrBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Or'Bv16'(src1,src2);
}

procedure {:inline 1} $XorBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Xor'Bv16'(src1,src2);
}

procedure {:inline 1} $LtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Lt'Bv16'(src1,src2);
}

procedure {:inline 1} $LeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Le'Bv16'(src1,src2);
}

procedure {:inline 1} $GtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Gt'Bv16'(src1,src2);
}

procedure {:inline 1} $GeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Ge'Bv16'(src1,src2);
}

function $IsValid'bv16'(v: bv16): bool {
  $Ge'Bv16'(v,0bv16) && $Le'Bv16'(v,65535bv16)
}

function {:inline} $IsEqual'bv16'(x: bv16, y: bv16): bool {
    x == y
}

procedure {:inline 1} $int2bv16(src: int) returns (dst: bv16)
{
    if (src > 65535) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.16(src);
}

procedure {:inline 1} $bv2int16(src: bv16) returns (dst: int)
{
    dst := $bv2int.16(src);
}

function {:builtin "(_ int2bv 16)"} $int2bv.16(i: int) returns (bv16);
function {:builtin "bv2nat"} $bv2int.16(i: bv16) returns (int);

function {:bvbuiltin "bvand"} $And'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} $Or'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxor"} $Xor'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} $Add'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $Sub'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $Mul'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} $Div'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} $Mod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $Shl'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $Shr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvult"} $Lt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv32'(bv32,bv32) returns(bool);

procedure {:inline 1} $AddBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Add'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $AddBv32_unchecked(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $SubBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv32'(src1, src2);
}

procedure {:inline 1} $MulBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Mul'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv32'(src1, src2);
}

procedure {:inline 1} $DivBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv32'(src1, src2);
}

procedure {:inline 1} $ModBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv32'(src1, src2);
}

procedure {:inline 1} $AndBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $And'Bv32'(src1,src2);
}

procedure {:inline 1} $OrBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Or'Bv32'(src1,src2);
}

procedure {:inline 1} $XorBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Xor'Bv32'(src1,src2);
}

procedure {:inline 1} $LtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Lt'Bv32'(src1,src2);
}

procedure {:inline 1} $LeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Le'Bv32'(src1,src2);
}

procedure {:inline 1} $GtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Gt'Bv32'(src1,src2);
}

procedure {:inline 1} $GeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Ge'Bv32'(src1,src2);
}

function $IsValid'bv32'(v: bv32): bool {
  $Ge'Bv32'(v,0bv32) && $Le'Bv32'(v,2147483647bv32)
}

function {:inline} $IsEqual'bv32'(x: bv32, y: bv32): bool {
    x == y
}

procedure {:inline 1} $int2bv32(src: int) returns (dst: bv32)
{
    if (src > 2147483647) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.32(src);
}

procedure {:inline 1} $bv2int32(src: bv32) returns (dst: int)
{
    dst := $bv2int.32(src);
}

function {:builtin "(_ int2bv 32)"} $int2bv.32(i: int) returns (bv32);
function {:builtin "bv2nat"} $bv2int.32(i: bv32) returns (int);

function {:bvbuiltin "bvand"} $And'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} $Or'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxor"} $Xor'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvadd"} $Add'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} $Sub'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} $Mul'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} $Div'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} $Mod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} $Shl'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} $Shr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvult"} $Lt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv64'(bv64,bv64) returns(bool);

procedure {:inline 1} $AddBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Add'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $AddBv64_unchecked(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $SubBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv64'(src1, src2);
}

procedure {:inline 1} $MulBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Mul'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv64'(src1, src2);
}

procedure {:inline 1} $DivBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv64'(src1, src2);
}

procedure {:inline 1} $ModBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv64'(src1, src2);
}

procedure {:inline 1} $AndBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $And'Bv64'(src1,src2);
}

procedure {:inline 1} $OrBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Or'Bv64'(src1,src2);
}

procedure {:inline 1} $XorBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Xor'Bv64'(src1,src2);
}

procedure {:inline 1} $LtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Lt'Bv64'(src1,src2);
}

procedure {:inline 1} $LeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Le'Bv64'(src1,src2);
}

procedure {:inline 1} $GtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Gt'Bv64'(src1,src2);
}

procedure {:inline 1} $GeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Ge'Bv64'(src1,src2);
}

function $IsValid'bv64'(v: bv64): bool {
  $Ge'Bv64'(v,0bv64) && $Le'Bv64'(v,18446744073709551615bv64)
}

function {:inline} $IsEqual'bv64'(x: bv64, y: bv64): bool {
    x == y
}

procedure {:inline 1} $int2bv64(src: int) returns (dst: bv64)
{
    if (src > 18446744073709551615) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.64(src);
}

procedure {:inline 1} $bv2int64(src: bv64) returns (dst: int)
{
    dst := $bv2int.64(src);
}

function {:builtin "(_ int2bv 64)"} $int2bv.64(i: int) returns (bv64);
function {:builtin "bv2nat"} $bv2int.64(i: bv64) returns (int);

function {:bvbuiltin "bvand"} $And'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvor"} $Or'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvxor"} $Xor'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvadd"} $Add'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsub"} $Sub'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvmul"} $Mul'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvudiv"} $Div'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvurem"} $Mod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvshl"} $Shl'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvlshr"} $Shr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvult"} $Lt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv128'(bv128,bv128) returns(bool);

procedure {:inline 1} $AddBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Add'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $AddBv128_unchecked(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $SubBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv128'(src1, src2);
}

procedure {:inline 1} $MulBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Mul'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv128'(src1, src2);
}

procedure {:inline 1} $DivBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv128'(src1, src2);
}

procedure {:inline 1} $ModBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv128'(src1, src2);
}

procedure {:inline 1} $AndBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $And'Bv128'(src1,src2);
}

procedure {:inline 1} $OrBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Or'Bv128'(src1,src2);
}

procedure {:inline 1} $XorBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Xor'Bv128'(src1,src2);
}

procedure {:inline 1} $LtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Lt'Bv128'(src1,src2);
}

procedure {:inline 1} $LeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Le'Bv128'(src1,src2);
}

procedure {:inline 1} $GtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Gt'Bv128'(src1,src2);
}

procedure {:inline 1} $GeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Ge'Bv128'(src1,src2);
}

function $IsValid'bv128'(v: bv128): bool {
  $Ge'Bv128'(v,0bv128) && $Le'Bv128'(v,340282366920938463463374607431768211455bv128)
}

function {:inline} $IsEqual'bv128'(x: bv128, y: bv128): bool {
    x == y
}

procedure {:inline 1} $int2bv128(src: int) returns (dst: bv128)
{
    if (src > 340282366920938463463374607431768211455) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.128(src);
}

procedure {:inline 1} $bv2int128(src: bv128) returns (dst: int)
{
    dst := $bv2int.128(src);
}

function {:builtin "(_ int2bv 128)"} $int2bv.128(i: int) returns (bv128);
function {:builtin "bv2nat"} $bv2int.128(i: bv128) returns (int);

function {:bvbuiltin "bvand"} $And'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvor"} $Or'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvxor"} $Xor'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvadd"} $Add'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsub"} $Sub'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvmul"} $Mul'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvudiv"} $Div'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvurem"} $Mod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvshl"} $Shl'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvlshr"} $Shr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvult"} $Lt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv256'(bv256,bv256) returns(bool);

procedure {:inline 1} $AddBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Add'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $AddBv256_unchecked(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $SubBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv256'(src1, src2);
}

procedure {:inline 1} $MulBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Mul'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv256'(src1, src2);
}

procedure {:inline 1} $DivBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv256'(src1, src2);
}

procedure {:inline 1} $ModBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv256'(src1, src2);
}

procedure {:inline 1} $AndBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $And'Bv256'(src1,src2);
}

procedure {:inline 1} $OrBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Or'Bv256'(src1,src2);
}

procedure {:inline 1} $XorBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Xor'Bv256'(src1,src2);
}

procedure {:inline 1} $LtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Lt'Bv256'(src1,src2);
}

procedure {:inline 1} $LeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Le'Bv256'(src1,src2);
}

procedure {:inline 1} $GtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Gt'Bv256'(src1,src2);
}

procedure {:inline 1} $GeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Ge'Bv256'(src1,src2);
}

function $IsValid'bv256'(v: bv256): bool {
  $Ge'Bv256'(v,0bv256) && $Le'Bv256'(v,115792089237316195423570985008687907853269984665640564039457584007913129639935bv256)
}

function {:inline} $IsEqual'bv256'(x: bv256, y: bv256): bool {
    x == y
}

procedure {:inline 1} $int2bv256(src: int) returns (dst: bv256)
{
    if (src > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.256(src);
}

procedure {:inline 1} $bv2int256(src: bv256) returns (dst: int)
{
    dst := $bv2int.256(src);
}

function {:builtin "(_ int2bv 256)"} $int2bv.256(i: int) returns (bv256);
function {:builtin "bv2nat"} $bv2int.256(i: bv256) returns (int);

datatype $Range {
    $Range(lb: int, ub: int)
}

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u16'(v: int): bool {
  v >= 0 && v <= $MAX_U16
}

function $IsValid'u32'(v: int): bool {
  v >= 0 && v <= $MAX_U32
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'u256'(v: int): bool {
  v >= 0 && v <= $MAX_U256
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(r->lb) &&  $IsValid'u64'(r->ub)
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   r->lb <= i && i < r->ub
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u256'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

datatype $Location {
    // A global resource location within the statically known resource type's memory,
    // where `a` is an address.
    $Global(a: int),
    // A local location. `i` is the unique index of the local.
    $Local(i: int),
    // The location of a reference outside of the verification scope, for example, a `&mut` parameter
    // of the function being verified. References with these locations don't need to be written back
    // when mutation ends.
    $Param(i: int),
    // The location of an uninitialized mutation. Using this to make sure that the location
    // will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
    $Uninitialized()
}

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
datatype $Mutation<T> {
    $Mutation(l: $Location, p: Vec int, v: T)
}

// Representation of memory for a given type.
datatype $Memory<T> {
    $Memory(domain: [int]bool, contents: [int]T)
}

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    ref->v
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(m->l, m->p, v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(m->l, ExtendVec(m->p, offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    parent->l == child->l && parent->p == child->p
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    m1->l == m2->l
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    (m->l) is $Global
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    m->l == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    (m->l)->a
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    m->domain[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    m->contents[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(m->domain[a := true], m->contents[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := false], m->contents)
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := s->domain[a]],
            m->contents[a := s->contents[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 256
}

function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 65536
}

function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 4294967296
}

function $shlU64(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 18446744073709551616
}

function $shlU128(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 340282366920938463463374607431768211456
}

function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/16/32/64/128/256
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU8(src1, src2);
}

// Template for cast and shift operations of bitvector types

procedure {:inline 1} $CastBv8to8(src: bv8) returns (dst: bv8)
{
    dst := src;
}


function $shlBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shl'Bv8'(src1, src2)
}

procedure {:inline 1} $ShlBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2);
}

function $shrBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shr'Bv8'(src1, src2)
}

procedure {:inline 1} $ShrBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2);
}

procedure {:inline 1} $CastBv16to8(src: bv16) returns (dst: bv8)
{
    if ($Gt'Bv16'(src, 255bv16)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv32to8(src: bv32) returns (dst: bv8)
{
    if ($Gt'Bv32'(src, 255bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv64to8(src: bv64) returns (dst: bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv128to8(src: bv128) returns (dst: bv8)
{
    if ($Gt'Bv128'(src, 255bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv256to8(src: bv256) returns (dst: bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv8to16(src: bv8) returns (dst: bv16)
{
    dst := 0bv8 ++ src;
}


function $shlBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shl'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShlBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, 0bv8 ++ src2);
}

function $shrBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shr'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShrBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, 0bv8 ++ src2);
}

procedure {:inline 1} $CastBv16to16(src: bv16) returns (dst: bv16)
{
    dst := src;
}


function $shlBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shl'Bv16'(src1, src2)
}

procedure {:inline 1} $ShlBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2);
}

function $shrBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shr'Bv16'(src1, src2)
}

procedure {:inline 1} $ShrBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2);
}

procedure {:inline 1} $CastBv32to16(src: bv32) returns (dst: bv16)
{
    if ($Gt'Bv32'(src, 65535bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv64to16(src: bv64) returns (dst: bv16)
{
    if ($Gt'Bv64'(src, 65535bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv128to16(src: bv128) returns (dst: bv16)
{
    if ($Gt'Bv128'(src, 65535bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv256to16(src: bv256) returns (dst: bv16)
{
    if ($Gt'Bv256'(src, 65535bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv8to32(src: bv8) returns (dst: bv32)
{
    dst := 0bv24 ++ src;
}


function $shlBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShlBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv24 ++ src2);
}

function $shrBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShrBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv24 ++ src2);
}

procedure {:inline 1} $CastBv16to32(src: bv16) returns (dst: bv32)
{
    dst := 0bv16 ++ src;
}


function $shlBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShlBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv16 ++ src2);
}

function $shrBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShrBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv16 ++ src2);
}

procedure {:inline 1} $CastBv32to32(src: bv32) returns (dst: bv32)
{
    dst := src;
}


function $shlBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shl'Bv32'(src1, src2)
}

procedure {:inline 1} $ShlBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2);
}

function $shrBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shr'Bv32'(src1, src2)
}

procedure {:inline 1} $ShrBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2);
}

procedure {:inline 1} $CastBv64to32(src: bv64) returns (dst: bv32)
{
    if ($Gt'Bv64'(src, 2147483647bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv128to32(src: bv128) returns (dst: bv32)
{
    if ($Gt'Bv128'(src, 2147483647bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv256to32(src: bv256) returns (dst: bv32)
{
    if ($Gt'Bv256'(src, 2147483647bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv8to64(src: bv8) returns (dst: bv64)
{
    dst := 0bv56 ++ src;
}


function $shlBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShlBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv56 ++ src2);
}

function $shrBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShrBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv56 ++ src2);
}

procedure {:inline 1} $CastBv16to64(src: bv16) returns (dst: bv64)
{
    dst := 0bv48 ++ src;
}


function $shlBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShlBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv48 ++ src2);
}

function $shrBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShrBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv48 ++ src2);
}

procedure {:inline 1} $CastBv32to64(src: bv32) returns (dst: bv64)
{
    dst := 0bv32 ++ src;
}


function $shlBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShlBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv32 ++ src2);
}

function $shrBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShrBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv32 ++ src2);
}

procedure {:inline 1} $CastBv64to64(src: bv64) returns (dst: bv64)
{
    dst := src;
}


function $shlBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shl'Bv64'(src1, src2)
}

procedure {:inline 1} $ShlBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2);
}

function $shrBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shr'Bv64'(src1, src2)
}

procedure {:inline 1} $ShrBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2);
}

procedure {:inline 1} $CastBv128to64(src: bv128) returns (dst: bv64)
{
    if ($Gt'Bv128'(src, 18446744073709551615bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv256to64(src: bv256) returns (dst: bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv8to128(src: bv8) returns (dst: bv128)
{
    dst := 0bv120 ++ src;
}


function $shlBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShlBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv120 ++ src2);
}

function $shrBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShrBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv120 ++ src2);
}

procedure {:inline 1} $CastBv16to128(src: bv16) returns (dst: bv128)
{
    dst := 0bv112 ++ src;
}


function $shlBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShlBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv112 ++ src2);
}

function $shrBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShrBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv112 ++ src2);
}

procedure {:inline 1} $CastBv32to128(src: bv32) returns (dst: bv128)
{
    dst := 0bv96 ++ src;
}


function $shlBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShlBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv96 ++ src2);
}

function $shrBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShrBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv96 ++ src2);
}

procedure {:inline 1} $CastBv64to128(src: bv64) returns (dst: bv128)
{
    dst := 0bv64 ++ src;
}


function $shlBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShlBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv64 ++ src2);
}

function $shrBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShrBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv64 ++ src2);
}

procedure {:inline 1} $CastBv128to128(src: bv128) returns (dst: bv128)
{
    dst := src;
}


function $shlBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shl'Bv128'(src1, src2)
}

procedure {:inline 1} $ShlBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2);
}

function $shrBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shr'Bv128'(src1, src2)
}

procedure {:inline 1} $ShrBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2);
}

procedure {:inline 1} $CastBv256to128(src: bv256) returns (dst: bv128)
{
    if ($Gt'Bv256'(src, 340282366920938463463374607431768211455bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[128:0];
}


function $shlBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shl'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShlBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2[128:0]);
}

function $shrBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shr'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShrBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2[128:0]);
}

procedure {:inline 1} $CastBv8to256(src: bv8) returns (dst: bv256)
{
    dst := 0bv248 ++ src;
}


function $shlBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShlBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv248 ++ src2);
}

function $shrBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShrBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv248 ++ src2);
}

procedure {:inline 1} $CastBv16to256(src: bv16) returns (dst: bv256)
{
    dst := 0bv240 ++ src;
}


function $shlBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShlBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv240 ++ src2);
}

function $shrBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShrBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv240 ++ src2);
}

procedure {:inline 1} $CastBv32to256(src: bv32) returns (dst: bv256)
{
    dst := 0bv224 ++ src;
}


function $shlBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShlBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv224 ++ src2);
}

function $shrBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShrBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv224 ++ src2);
}

procedure {:inline 1} $CastBv64to256(src: bv64) returns (dst: bv256)
{
    dst := 0bv192 ++ src;
}


function $shlBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShlBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv192 ++ src2);
}

function $shrBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShrBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv192 ++ src2);
}

procedure {:inline 1} $CastBv128to256(src: bv128) returns (dst: bv256)
{
    dst := 0bv128 ++ src;
}


function $shlBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShlBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv128 ++ src2);
}

function $shrBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShrBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv128 ++ src2);
}

procedure {:inline 1} $CastBv256to256(src: bv256) returns (dst: bv256)
{
    dst := src;
}


function $shlBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shl'Bv256'(src1, src2)
}

procedure {:inline 1} $ShlBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, src2);
}

function $shrBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shr'Bv256'(src1, src2)
}

procedure {:inline 1} $ShrBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, src2);
}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
       call $ExecFailureAbort();
       return;
    }
    dst := $shlU64(src1, src2);
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU128(src1, src2);
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, r->lb, r->ub)
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `#0`

// Not inlined. It appears faster this way.
function $IsEqual'vec'#0''(v1: Vec (#0), v2: Vec (#0)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'#0'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'#0''(v: Vec (#0), prefix: Vec (#0)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'#0'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'#0''(v: Vec (#0), suffix: Vec (#0)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'#0'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'#0''(v: Vec (#0)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'#0'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'#0'(v: Vec (#0), e: #0): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'#0'(ReadVec(v, i), e))
}

function $IndexOfVec'#0'(v: Vec (#0), e: #0): int;
axiom (forall v: Vec (#0), e: #0:: {$IndexOfVec'#0'(v, e)}
    (var i := $IndexOfVec'#0'(v, e);
     if (!$ContainsVec'#0'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'#0'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'#0'(ReadVec(v, j), e))));


function {:inline} $RangeVec'#0'(v: Vec (#0)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'#0'(): Vec (#0) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'#0'() returns (v: Vec (#0)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'#0'(): Vec (#0) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'#0'(v: Vec (#0)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'#0'(m: $Mutation (Vec (#0)), val: #0) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'#0'(v: Vec (#0), val: #0): Vec (#0) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'#0'(m: $Mutation (Vec (#0))) returns (e: #0, m': $Mutation (Vec (#0))) {
    var v: Vec (#0);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'#0'(m: $Mutation (Vec (#0)), other: Vec (#0)) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'#0'(m: $Mutation (Vec (#0))) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'#0'(m: $Mutation (Vec (#0)), other: Vec (#0)) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'#0'(m: $Mutation (Vec (#0)), new_len: int) returns (v: (Vec (#0)), m': $Mutation (Vec (#0))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'#0'(m: $Mutation (Vec (#0)), new_len: int) returns (v: (Vec (#0)), m': $Mutation (Vec (#0))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'#0'(m: $Mutation (Vec (#0)), left: int, right: int) returns (m': $Mutation (Vec (#0))) {
    var left_vec: Vec (#0);
    var mid_vec: Vec (#0);
    var right_vec: Vec (#0);
    var v: Vec (#0);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'#0'(m: $Mutation (Vec (#0)), rot: int) returns (n: int, m': $Mutation (Vec (#0))) {
    var v: Vec (#0);
    var len: int;
    var left_vec: Vec (#0);
    var right_vec: Vec (#0);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'#0'(m: $Mutation (Vec (#0)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (#0))) {
    var left_vec: Vec (#0);
    var mid_vec: Vec (#0);
    var right_vec: Vec (#0);
    var mid_left_vec: Vec (#0);
    var mid_right_vec: Vec (#0);
    var v: Vec (#0);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'#0'(m: $Mutation (Vec (#0)), i: int, e: #0) returns (m': $Mutation (Vec (#0))) {
    var left_vec: Vec (#0);
    var right_vec: Vec (#0);
    var v: Vec (#0);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'#0'(v: Vec (#0)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'#0'(v: Vec (#0)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'#0'(v: Vec (#0), i: int) returns (dst: #0) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'#0'(v: Vec (#0), i: int): #0 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'#0'(m: $Mutation (Vec (#0)), index: int)
returns (dst: $Mutation (#0), m': $Mutation (Vec (#0)))
{
    var v: Vec (#0);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'#0'(v: Vec (#0), i: int): #0 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'#0'(v: Vec (#0)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'#0'(m: $Mutation (Vec (#0)), i: int, j: int) returns (m': $Mutation (Vec (#0)))
{
    var v: Vec (#0);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'#0'(v: Vec (#0), i: int, j: int): Vec (#0) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'#0'(m: $Mutation (Vec (#0)), i: int) returns (e: #0, m': $Mutation (Vec (#0)))
{
    var v: Vec (#0);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'#0'(m: $Mutation (Vec (#0)), i: int) returns (e: #0, m': $Mutation (Vec (#0)))
{
    var len: int;
    var v: Vec (#0);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'#0'(v: Vec (#0), e: #0) returns (res: bool)  {
    res := $ContainsVec'#0'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'#0'(v: Vec (#0), e: #0) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'#0'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$1_big_vector_BigVector'address'`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_big_vector_BigVector'address'''(v1: Vec ($1_big_vector_BigVector'address'), v2: Vec ($1_big_vector_BigVector'address')): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_big_vector_BigVector'address''(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_big_vector_BigVector'address'''(v: Vec ($1_big_vector_BigVector'address'), prefix: Vec ($1_big_vector_BigVector'address')): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_big_vector_BigVector'address''(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_big_vector_BigVector'address'''(v: Vec ($1_big_vector_BigVector'address'), suffix: Vec ($1_big_vector_BigVector'address')): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_big_vector_BigVector'address''(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_big_vector_BigVector'address'''(v: Vec ($1_big_vector_BigVector'address')): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_big_vector_BigVector'address''(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address'), e: $1_big_vector_BigVector'address'): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_big_vector_BigVector'address''(ReadVec(v, i), e))
}

function $IndexOfVec'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address'), e: $1_big_vector_BigVector'address'): int;
axiom (forall v: Vec ($1_big_vector_BigVector'address'), e: $1_big_vector_BigVector'address':: {$IndexOfVec'$1_big_vector_BigVector'address''(v, e)}
    (var i := $IndexOfVec'$1_big_vector_BigVector'address''(v, e);
     if (!$ContainsVec'$1_big_vector_BigVector'address''(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_big_vector_BigVector'address''(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_big_vector_BigVector'address''(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address')): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_big_vector_BigVector'address''(): Vec ($1_big_vector_BigVector'address') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_big_vector_BigVector'address''() returns (v: Vec ($1_big_vector_BigVector'address')) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_big_vector_BigVector'address''(): Vec ($1_big_vector_BigVector'address') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address')) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), val: $1_big_vector_BigVector'address') returns (m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address'), val: $1_big_vector_BigVector'address'): Vec ($1_big_vector_BigVector'address') {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address'))) returns (e: $1_big_vector_BigVector'address', m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    var v: Vec ($1_big_vector_BigVector'address');
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), other: Vec ($1_big_vector_BigVector'address')) returns (m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address'))) returns (m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), other: Vec ($1_big_vector_BigVector'address')) returns (m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), new_len: int) returns (v: (Vec ($1_big_vector_BigVector'address')), m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), new_len: int) returns (v: (Vec ($1_big_vector_BigVector'address')), m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), left: int, right: int) returns (m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    var left_vec: Vec ($1_big_vector_BigVector'address');
    var mid_vec: Vec ($1_big_vector_BigVector'address');
    var right_vec: Vec ($1_big_vector_BigVector'address');
    var v: Vec ($1_big_vector_BigVector'address');
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), rot: int) returns (n: int, m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    var v: Vec ($1_big_vector_BigVector'address');
    var len: int;
    var left_vec: Vec ($1_big_vector_BigVector'address');
    var right_vec: Vec ($1_big_vector_BigVector'address');
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    var left_vec: Vec ($1_big_vector_BigVector'address');
    var mid_vec: Vec ($1_big_vector_BigVector'address');
    var right_vec: Vec ($1_big_vector_BigVector'address');
    var mid_left_vec: Vec ($1_big_vector_BigVector'address');
    var mid_right_vec: Vec ($1_big_vector_BigVector'address');
    var v: Vec ($1_big_vector_BigVector'address');
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), i: int, e: $1_big_vector_BigVector'address') returns (m': $Mutation (Vec ($1_big_vector_BigVector'address'))) {
    var left_vec: Vec ($1_big_vector_BigVector'address');
    var right_vec: Vec ($1_big_vector_BigVector'address');
    var v: Vec ($1_big_vector_BigVector'address');
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address')) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address')): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address'), i: int) returns (dst: $1_big_vector_BigVector'address') {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address'), i: int): $1_big_vector_BigVector'address' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), index: int)
returns (dst: $Mutation ($1_big_vector_BigVector'address'), m': $Mutation (Vec ($1_big_vector_BigVector'address')))
{
    var v: Vec ($1_big_vector_BigVector'address');
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address'), i: int): $1_big_vector_BigVector'address' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address')) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), i: int, j: int) returns (m': $Mutation (Vec ($1_big_vector_BigVector'address')))
{
    var v: Vec ($1_big_vector_BigVector'address');
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address'), i: int, j: int): Vec ($1_big_vector_BigVector'address') {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), i: int) returns (e: $1_big_vector_BigVector'address', m': $Mutation (Vec ($1_big_vector_BigVector'address')))
{
    var v: Vec ($1_big_vector_BigVector'address');

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_big_vector_BigVector'address''(m: $Mutation (Vec ($1_big_vector_BigVector'address')), i: int) returns (e: $1_big_vector_BigVector'address', m': $Mutation (Vec ($1_big_vector_BigVector'address')))
{
    var len: int;
    var v: Vec ($1_big_vector_BigVector'address');

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address'), e: $1_big_vector_BigVector'address') returns (res: bool)  {
    res := $ContainsVec'$1_big_vector_BigVector'address''(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_big_vector_BigVector'address''(v: Vec ($1_big_vector_BigVector'address'), e: $1_big_vector_BigVector'address') returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_big_vector_BigVector'address''(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$1_fungible_asset_FungibleAsset`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_fungible_asset_FungibleAsset''(v1: Vec ($1_fungible_asset_FungibleAsset), v2: Vec ($1_fungible_asset_FungibleAsset)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_fungible_asset_FungibleAsset'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_fungible_asset_FungibleAsset''(v: Vec ($1_fungible_asset_FungibleAsset), prefix: Vec ($1_fungible_asset_FungibleAsset)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_fungible_asset_FungibleAsset'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_fungible_asset_FungibleAsset''(v: Vec ($1_fungible_asset_FungibleAsset), suffix: Vec ($1_fungible_asset_FungibleAsset)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_fungible_asset_FungibleAsset'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_fungible_asset_FungibleAsset''(v: Vec ($1_fungible_asset_FungibleAsset)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_fungible_asset_FungibleAsset'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset), e: $1_fungible_asset_FungibleAsset): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_fungible_asset_FungibleAsset'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset), e: $1_fungible_asset_FungibleAsset): int;
axiom (forall v: Vec ($1_fungible_asset_FungibleAsset), e: $1_fungible_asset_FungibleAsset:: {$IndexOfVec'$1_fungible_asset_FungibleAsset'(v, e)}
    (var i := $IndexOfVec'$1_fungible_asset_FungibleAsset'(v, e);
     if (!$ContainsVec'$1_fungible_asset_FungibleAsset'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_fungible_asset_FungibleAsset'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_fungible_asset_FungibleAsset'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_fungible_asset_FungibleAsset'(): Vec ($1_fungible_asset_FungibleAsset) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_fungible_asset_FungibleAsset'() returns (v: Vec ($1_fungible_asset_FungibleAsset)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_fungible_asset_FungibleAsset'(): Vec ($1_fungible_asset_FungibleAsset) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), val: $1_fungible_asset_FungibleAsset) returns (m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset), val: $1_fungible_asset_FungibleAsset): Vec ($1_fungible_asset_FungibleAsset) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset))) returns (e: $1_fungible_asset_FungibleAsset, m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    var v: Vec ($1_fungible_asset_FungibleAsset);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), other: Vec ($1_fungible_asset_FungibleAsset)) returns (m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset))) returns (m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), other: Vec ($1_fungible_asset_FungibleAsset)) returns (m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), new_len: int) returns (v: (Vec ($1_fungible_asset_FungibleAsset)), m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), new_len: int) returns (v: (Vec ($1_fungible_asset_FungibleAsset)), m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), left: int, right: int) returns (m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    var left_vec: Vec ($1_fungible_asset_FungibleAsset);
    var mid_vec: Vec ($1_fungible_asset_FungibleAsset);
    var right_vec: Vec ($1_fungible_asset_FungibleAsset);
    var v: Vec ($1_fungible_asset_FungibleAsset);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), rot: int) returns (n: int, m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    var v: Vec ($1_fungible_asset_FungibleAsset);
    var len: int;
    var left_vec: Vec ($1_fungible_asset_FungibleAsset);
    var right_vec: Vec ($1_fungible_asset_FungibleAsset);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    var left_vec: Vec ($1_fungible_asset_FungibleAsset);
    var mid_vec: Vec ($1_fungible_asset_FungibleAsset);
    var right_vec: Vec ($1_fungible_asset_FungibleAsset);
    var mid_left_vec: Vec ($1_fungible_asset_FungibleAsset);
    var mid_right_vec: Vec ($1_fungible_asset_FungibleAsset);
    var v: Vec ($1_fungible_asset_FungibleAsset);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), i: int, e: $1_fungible_asset_FungibleAsset) returns (m': $Mutation (Vec ($1_fungible_asset_FungibleAsset))) {
    var left_vec: Vec ($1_fungible_asset_FungibleAsset);
    var right_vec: Vec ($1_fungible_asset_FungibleAsset);
    var v: Vec ($1_fungible_asset_FungibleAsset);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset), i: int) returns (dst: $1_fungible_asset_FungibleAsset) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset), i: int): $1_fungible_asset_FungibleAsset {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), index: int)
returns (dst: $Mutation ($1_fungible_asset_FungibleAsset), m': $Mutation (Vec ($1_fungible_asset_FungibleAsset)))
{
    var v: Vec ($1_fungible_asset_FungibleAsset);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset), i: int): $1_fungible_asset_FungibleAsset {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), i: int, j: int) returns (m': $Mutation (Vec ($1_fungible_asset_FungibleAsset)))
{
    var v: Vec ($1_fungible_asset_FungibleAsset);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset), i: int, j: int): Vec ($1_fungible_asset_FungibleAsset) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), i: int) returns (e: $1_fungible_asset_FungibleAsset, m': $Mutation (Vec ($1_fungible_asset_FungibleAsset)))
{
    var v: Vec ($1_fungible_asset_FungibleAsset);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_fungible_asset_FungibleAsset'(m: $Mutation (Vec ($1_fungible_asset_FungibleAsset)), i: int) returns (e: $1_fungible_asset_FungibleAsset, m': $Mutation (Vec ($1_fungible_asset_FungibleAsset)))
{
    var len: int;
    var v: Vec ($1_fungible_asset_FungibleAsset);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset), e: $1_fungible_asset_FungibleAsset) returns (res: bool)  {
    res := $ContainsVec'$1_fungible_asset_FungibleAsset'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_fungible_asset_FungibleAsset'(v: Vec ($1_fungible_asset_FungibleAsset), e: $1_fungible_asset_FungibleAsset) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_fungible_asset_FungibleAsset'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$aa_rewarder_Rewarder`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$aa_rewarder_Rewarder''(v1: Vec ($aa_rewarder_Rewarder), v2: Vec ($aa_rewarder_Rewarder)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$aa_rewarder_Rewarder'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$aa_rewarder_Rewarder''(v: Vec ($aa_rewarder_Rewarder), prefix: Vec ($aa_rewarder_Rewarder)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$aa_rewarder_Rewarder'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$aa_rewarder_Rewarder''(v: Vec ($aa_rewarder_Rewarder), suffix: Vec ($aa_rewarder_Rewarder)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$aa_rewarder_Rewarder'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$aa_rewarder_Rewarder''(v: Vec ($aa_rewarder_Rewarder)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$aa_rewarder_Rewarder'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder), e: $aa_rewarder_Rewarder): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$aa_rewarder_Rewarder'(ReadVec(v, i), e))
}

function $IndexOfVec'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder), e: $aa_rewarder_Rewarder): int;
axiom (forall v: Vec ($aa_rewarder_Rewarder), e: $aa_rewarder_Rewarder:: {$IndexOfVec'$aa_rewarder_Rewarder'(v, e)}
    (var i := $IndexOfVec'$aa_rewarder_Rewarder'(v, e);
     if (!$ContainsVec'$aa_rewarder_Rewarder'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$aa_rewarder_Rewarder'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$aa_rewarder_Rewarder'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$aa_rewarder_Rewarder'(): Vec ($aa_rewarder_Rewarder) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$aa_rewarder_Rewarder'() returns (v: Vec ($aa_rewarder_Rewarder)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$aa_rewarder_Rewarder'(): Vec ($aa_rewarder_Rewarder) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), val: $aa_rewarder_Rewarder) returns (m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder), val: $aa_rewarder_Rewarder): Vec ($aa_rewarder_Rewarder) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder))) returns (e: $aa_rewarder_Rewarder, m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    var v: Vec ($aa_rewarder_Rewarder);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), other: Vec ($aa_rewarder_Rewarder)) returns (m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder))) returns (m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), other: Vec ($aa_rewarder_Rewarder)) returns (m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), new_len: int) returns (v: (Vec ($aa_rewarder_Rewarder)), m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), new_len: int) returns (v: (Vec ($aa_rewarder_Rewarder)), m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), left: int, right: int) returns (m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    var left_vec: Vec ($aa_rewarder_Rewarder);
    var mid_vec: Vec ($aa_rewarder_Rewarder);
    var right_vec: Vec ($aa_rewarder_Rewarder);
    var v: Vec ($aa_rewarder_Rewarder);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), rot: int) returns (n: int, m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    var v: Vec ($aa_rewarder_Rewarder);
    var len: int;
    var left_vec: Vec ($aa_rewarder_Rewarder);
    var right_vec: Vec ($aa_rewarder_Rewarder);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    var left_vec: Vec ($aa_rewarder_Rewarder);
    var mid_vec: Vec ($aa_rewarder_Rewarder);
    var right_vec: Vec ($aa_rewarder_Rewarder);
    var mid_left_vec: Vec ($aa_rewarder_Rewarder);
    var mid_right_vec: Vec ($aa_rewarder_Rewarder);
    var v: Vec ($aa_rewarder_Rewarder);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), i: int, e: $aa_rewarder_Rewarder) returns (m': $Mutation (Vec ($aa_rewarder_Rewarder))) {
    var left_vec: Vec ($aa_rewarder_Rewarder);
    var right_vec: Vec ($aa_rewarder_Rewarder);
    var v: Vec ($aa_rewarder_Rewarder);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder), i: int) returns (dst: $aa_rewarder_Rewarder) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder), i: int): $aa_rewarder_Rewarder {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), index: int)
returns (dst: $Mutation ($aa_rewarder_Rewarder), m': $Mutation (Vec ($aa_rewarder_Rewarder)))
{
    var v: Vec ($aa_rewarder_Rewarder);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder), i: int): $aa_rewarder_Rewarder {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), i: int, j: int) returns (m': $Mutation (Vec ($aa_rewarder_Rewarder)))
{
    var v: Vec ($aa_rewarder_Rewarder);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder), i: int, j: int): Vec ($aa_rewarder_Rewarder) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), i: int) returns (e: $aa_rewarder_Rewarder, m': $Mutation (Vec ($aa_rewarder_Rewarder)))
{
    var v: Vec ($aa_rewarder_Rewarder);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$aa_rewarder_Rewarder'(m: $Mutation (Vec ($aa_rewarder_Rewarder)), i: int) returns (e: $aa_rewarder_Rewarder, m': $Mutation (Vec ($aa_rewarder_Rewarder)))
{
    var len: int;
    var v: Vec ($aa_rewarder_Rewarder);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder), e: $aa_rewarder_Rewarder) returns (res: bool)  {
    res := $ContainsVec'$aa_rewarder_Rewarder'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$aa_rewarder_Rewarder'(v: Vec ($aa_rewarder_Rewarder), e: $aa_rewarder_Rewarder) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$aa_rewarder_Rewarder'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `address`

// Not inlined. It appears faster this way.
function $IsEqual'vec'address''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'address'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'address''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'address'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'address''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'address'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'address''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'address'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'address'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'address'(ReadVec(v, i), e))
}

function $IndexOfVec'address'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'address'(v, e)}
    (var i := $IndexOfVec'address'(v, e);
     if (!$ContainsVec'address'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'address'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'address'(ReadVec(v, j), e))));


function {:inline} $RangeVec'address'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'address'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'address'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'address'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'address'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'address'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'address'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'address'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'address'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'address'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'address'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'address'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'address'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'address'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'address'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'address'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'address'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'address'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'address'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'address'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'address'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'address'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'address'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'address'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'address'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'address'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'address'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'address'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'address'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'address'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'address'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'address'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u128`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u128''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u128'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u128''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u128'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u128''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u128'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u128''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u128'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u128'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u128'(ReadVec(v, i), e))
}

function $IndexOfVec'u128'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u128'(v, e)}
    (var i := $IndexOfVec'u128'(v, e);
     if (!$ContainsVec'u128'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u128'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u128'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u128'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u128'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u128'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u128'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u128'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u128'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u128'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u128'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u128'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u128'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u128'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u128'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u128'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u128'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u128'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u128'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u128'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u128'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u128'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u128'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u128'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u128'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u128'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u128'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u128'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u128'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u128'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u128'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u128'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u128'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u128'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u128'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u64`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u64''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u64'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u64''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u64'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u64''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u64'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u64''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u64'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u64'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e))
}

function $IndexOfVec'u64'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u64'(v, e)}
    (var i := $IndexOfVec'u64'(v, e);
     if (!$ContainsVec'u64'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u64'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u64'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u64'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u64'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u64'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u64'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u64'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u64'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u64'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u64'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u64'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u64'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u64'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u64'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u64'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u64'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u64'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u64'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u64'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u64'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u64'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u64'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u64'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u64'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u64'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u64'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u64'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u8''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u8''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u8'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u8'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u8'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u8'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv128`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv128''(v1: Vec (bv128), v2: Vec (bv128)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv128'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv128''(v: Vec (bv128), prefix: Vec (bv128)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv128'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv128''(v: Vec (bv128), suffix: Vec (bv128)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv128'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv128''(v: Vec (bv128)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv128'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'bv128'(v: Vec (bv128), e: bv128): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv128'(ReadVec(v, i), e))
}

function $IndexOfVec'bv128'(v: Vec (bv128), e: bv128): int;
axiom (forall v: Vec (bv128), e: bv128:: {$IndexOfVec'bv128'(v, e)}
    (var i := $IndexOfVec'bv128'(v, e);
     if (!$ContainsVec'bv128'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv128'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv128'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv128'(v: Vec (bv128)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv128'(): Vec (bv128) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv128'() returns (v: Vec (bv128)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv128'(): Vec (bv128) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv128'(v: Vec (bv128)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv128'(m: $Mutation (Vec (bv128)), val: bv128) returns (m': $Mutation (Vec (bv128))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv128'(v: Vec (bv128), val: bv128): Vec (bv128) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv128'(m: $Mutation (Vec (bv128))) returns (e: bv128, m': $Mutation (Vec (bv128))) {
    var v: Vec (bv128);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bv128'(m: $Mutation (Vec (bv128)), other: Vec (bv128)) returns (m': $Mutation (Vec (bv128))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv128'(m: $Mutation (Vec (bv128))) returns (m': $Mutation (Vec (bv128))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv128'(m: $Mutation (Vec (bv128)), other: Vec (bv128)) returns (m': $Mutation (Vec (bv128))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv128'(m: $Mutation (Vec (bv128)), new_len: int) returns (v: (Vec (bv128)), m': $Mutation (Vec (bv128))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'bv128'(m: $Mutation (Vec (bv128)), new_len: int) returns (v: (Vec (bv128)), m': $Mutation (Vec (bv128))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv128'(m: $Mutation (Vec (bv128)), left: int, right: int) returns (m': $Mutation (Vec (bv128))) {
    var left_vec: Vec (bv128);
    var mid_vec: Vec (bv128);
    var right_vec: Vec (bv128);
    var v: Vec (bv128);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'bv128'(m: $Mutation (Vec (bv128)), rot: int) returns (n: int, m': $Mutation (Vec (bv128))) {
    var v: Vec (bv128);
    var len: int;
    var left_vec: Vec (bv128);
    var right_vec: Vec (bv128);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'bv128'(m: $Mutation (Vec (bv128)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv128))) {
    var left_vec: Vec (bv128);
    var mid_vec: Vec (bv128);
    var right_vec: Vec (bv128);
    var mid_left_vec: Vec (bv128);
    var mid_right_vec: Vec (bv128);
    var v: Vec (bv128);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'bv128'(m: $Mutation (Vec (bv128)), i: int, e: bv128) returns (m': $Mutation (Vec (bv128))) {
    var left_vec: Vec (bv128);
    var right_vec: Vec (bv128);
    var v: Vec (bv128);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'bv128'(v: Vec (bv128)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv128'(v: Vec (bv128)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv128'(v: Vec (bv128), i: int) returns (dst: bv128) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv128'(v: Vec (bv128), i: int): bv128 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv128'(m: $Mutation (Vec (bv128)), index: int)
returns (dst: $Mutation (bv128), m': $Mutation (Vec (bv128)))
{
    var v: Vec (bv128);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv128'(v: Vec (bv128), i: int): bv128 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv128'(v: Vec (bv128)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv128'(m: $Mutation (Vec (bv128)), i: int, j: int) returns (m': $Mutation (Vec (bv128)))
{
    var v: Vec (bv128);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv128'(v: Vec (bv128), i: int, j: int): Vec (bv128) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv128'(m: $Mutation (Vec (bv128)), i: int) returns (e: bv128, m': $Mutation (Vec (bv128)))
{
    var v: Vec (bv128);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv128'(m: $Mutation (Vec (bv128)), i: int) returns (e: bv128, m': $Mutation (Vec (bv128)))
{
    var len: int;
    var v: Vec (bv128);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv128'(v: Vec (bv128), e: bv128) returns (res: bool)  {
    res := $ContainsVec'bv128'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv128'(v: Vec (bv128), e: bv128) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv128'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv64`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv64''(v1: Vec (bv64), v2: Vec (bv64)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv64'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv64''(v: Vec (bv64), prefix: Vec (bv64)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv64'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv64''(v: Vec (bv64), suffix: Vec (bv64)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv64'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv64''(v: Vec (bv64)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv64'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'bv64'(v: Vec (bv64), e: bv64): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv64'(ReadVec(v, i), e))
}

function $IndexOfVec'bv64'(v: Vec (bv64), e: bv64): int;
axiom (forall v: Vec (bv64), e: bv64:: {$IndexOfVec'bv64'(v, e)}
    (var i := $IndexOfVec'bv64'(v, e);
     if (!$ContainsVec'bv64'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv64'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv64'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv64'(v: Vec (bv64)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv64'(): Vec (bv64) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv64'() returns (v: Vec (bv64)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv64'(): Vec (bv64) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv64'(v: Vec (bv64)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv64'(m: $Mutation (Vec (bv64)), val: bv64) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv64'(v: Vec (bv64), val: bv64): Vec (bv64) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv64'(m: $Mutation (Vec (bv64))) returns (e: bv64, m': $Mutation (Vec (bv64))) {
    var v: Vec (bv64);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bv64'(m: $Mutation (Vec (bv64)), other: Vec (bv64)) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv64'(m: $Mutation (Vec (bv64))) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv64'(m: $Mutation (Vec (bv64)), other: Vec (bv64)) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv64'(m: $Mutation (Vec (bv64)), new_len: int) returns (v: (Vec (bv64)), m': $Mutation (Vec (bv64))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'bv64'(m: $Mutation (Vec (bv64)), new_len: int) returns (v: (Vec (bv64)), m': $Mutation (Vec (bv64))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv64'(m: $Mutation (Vec (bv64)), left: int, right: int) returns (m': $Mutation (Vec (bv64))) {
    var left_vec: Vec (bv64);
    var mid_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    var v: Vec (bv64);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'bv64'(m: $Mutation (Vec (bv64)), rot: int) returns (n: int, m': $Mutation (Vec (bv64))) {
    var v: Vec (bv64);
    var len: int;
    var left_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'bv64'(m: $Mutation (Vec (bv64)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv64))) {
    var left_vec: Vec (bv64);
    var mid_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    var mid_left_vec: Vec (bv64);
    var mid_right_vec: Vec (bv64);
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'bv64'(m: $Mutation (Vec (bv64)), i: int, e: bv64) returns (m': $Mutation (Vec (bv64))) {
    var left_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'bv64'(v: Vec (bv64)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv64'(v: Vec (bv64)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv64'(v: Vec (bv64), i: int) returns (dst: bv64) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv64'(v: Vec (bv64), i: int): bv64 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv64'(m: $Mutation (Vec (bv64)), index: int)
returns (dst: $Mutation (bv64), m': $Mutation (Vec (bv64)))
{
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv64'(v: Vec (bv64), i: int): bv64 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv64'(v: Vec (bv64)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv64'(m: $Mutation (Vec (bv64)), i: int, j: int) returns (m': $Mutation (Vec (bv64)))
{
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv64'(v: Vec (bv64), i: int, j: int): Vec (bv64) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv64'(m: $Mutation (Vec (bv64)), i: int) returns (e: bv64, m': $Mutation (Vec (bv64)))
{
    var v: Vec (bv64);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv64'(m: $Mutation (Vec (bv64)), i: int) returns (e: bv64, m': $Mutation (Vec (bv64)))
{
    var len: int;
    var v: Vec (bv64);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv64'(v: Vec (bv64), e: bv64) returns (res: bool)  {
    res := $ContainsVec'bv64'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv64'(v: Vec (bv64), e: bv64) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv64'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv8''(v1: Vec (bv8), v2: Vec (bv8)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv8''(v: Vec (bv8), prefix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv8''(v: Vec (bv8), suffix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv8''(v: Vec (bv8)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'bv8'(v: Vec (bv8), e: bv8): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e))
}

function $IndexOfVec'bv8'(v: Vec (bv8), e: bv8): int;
axiom (forall v: Vec (bv8), e: bv8:: {$IndexOfVec'bv8'(v, e)}
    (var i := $IndexOfVec'bv8'(v, e);
     if (!$ContainsVec'bv8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv8'(v: Vec (bv8)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv8'() returns (v: Vec (bv8)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv8'(v: Vec (bv8)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv8'(m: $Mutation (Vec (bv8)), val: bv8) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv8'(v: Vec (bv8), val: bv8): Vec (bv8) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv8'(m: $Mutation (Vec (bv8))) returns (e: bv8, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv8'(m: $Mutation (Vec (bv8))) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, right: int) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'bv8'(m: $Mutation (Vec (bv8)), rot: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var mid_left_vec: Vec (bv8);
    var mid_right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'bv8'(m: $Mutation (Vec (bv8)), i: int, e: bv8) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'bv8'(v: Vec (bv8)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv8'(v: Vec (bv8)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv8'(v: Vec (bv8), i: int) returns (dst: bv8) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv8'(m: $Mutation (Vec (bv8)), index: int)
returns (dst: $Mutation (bv8), m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv8'(v: Vec (bv8)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv8'(m: $Mutation (Vec (bv8)), i: int, j: int) returns (m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv8'(v: Vec (bv8), i: int, j: int): Vec (bv8) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var len: int;
    var v: Vec (bv8);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv8'(v: Vec (bv8), e: bv8) returns (res: bool)  {
    res := $ContainsVec'bv8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv8'(v: Vec (bv8), e: bv8) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ----------------------------------------------------------------------------------
// Native Table key encoding for type `$aa_i32_I32`

function $EncodeKey'$aa_i32_I32'(k: $aa_i32_I32): int;
axiom (
  forall k1, k2: $aa_i32_I32 :: {$EncodeKey'$aa_i32_I32'(k1), $EncodeKey'$aa_i32_I32'(k2)}
    $IsEqual'$aa_i32_I32'(k1, k2) <==> $EncodeKey'$aa_i32_I32'(k1) == $EncodeKey'$aa_i32_I32'(k2)
);


// ----------------------------------------------------------------------------------
// Native Table key encoding for type `u64`

function $EncodeKey'u64'(k: int): int;
axiom (
  forall k1, k2: int :: {$EncodeKey'u64'(k1), $EncodeKey'u64'(k2)}
    $IsEqual'u64'(k1, k2) <==> $EncodeKey'u64'(k1) == $EncodeKey'u64'(k2)
);


// ----------------------------------------------------------------------------------
// Native Table implementation for type `($aa_i32_I32,u256)`

function $IsEqual'$1_table_Table'$aa_i32_I32_u256''(t1: Table int (int), t2: Table int (int)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_table_Table'$aa_i32_I32_u256''(t: Table int (int)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'u256'(GetTable(t, i)))
}
procedure {:inline 2} $1_table_new'$aa_i32_I32_u256'() returns (v: Table int (int)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_table_destroy_known_empty_unsafe'$aa_i32_I32_u256'(t: Table int (int)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_table_contains'$aa_i32_I32_u256'(t: (Table int (int)), k: $aa_i32_I32) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'$aa_i32_I32'(k));
}
procedure {:inline 2} $1_table_add'$aa_i32_I32_u256'(m: $Mutation (Table int (int)), k: $aa_i32_I32, v: int) returns (m': $Mutation(Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_upsert'$aa_i32_I32_u256'(m: $Mutation (Table int (int)), k: $aa_i32_I32, v: int) returns (m': $Mutation(Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, UpdateTable(t, enc_k, v));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_remove'$aa_i32_I32_u256'(m: $Mutation (Table int (int)), k: $aa_i32_I32)
returns (v: int, m': $Mutation(Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_table_borrow'$aa_i32_I32_u256'(t: Table int (int), k: $aa_i32_I32) returns (v: int) {
    var enc_k: int;
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'$aa_i32_I32'(k));
    }
}
procedure {:inline 2} $1_table_borrow_mut'$aa_i32_I32_u256'(m: $Mutation (Table int (int)), k: $aa_i32_I32)
returns (dst: $Mutation (int), m': $Mutation (Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
procedure {:inline 2} $1_table_borrow_mut_with_default'$aa_i32_I32_u256'(m: $Mutation (Table int (int)), k: $aa_i32_I32, default: int)
returns (dst: $Mutation (int), m': $Mutation (Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    var t': Table int (int);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, AddTable(t, enc_k, default));
        t' := $Dereference(m');
        dst := $Mutation(m'->l, ExtendVec(m'->p, enc_k), GetTable(t', enc_k));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_table_spec_contains'$aa_i32_I32_u256'(t: (Table int (int)), k: $aa_i32_I32): bool {
    ContainsTable(t, $EncodeKey'$aa_i32_I32'(k))
}
function {:inline} $1_table_spec_set'$aa_i32_I32_u256'(t: Table int (int), k: $aa_i32_I32, v: int): Table int (int) {
    (var enc_k := $EncodeKey'$aa_i32_I32'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_table_spec_remove'$aa_i32_I32_u256'(t: Table int (int), k: $aa_i32_I32): Table int (int) {
    RemoveTable(t, $EncodeKey'$aa_i32_I32'(k))
}
function {:inline} $1_table_spec_get'$aa_i32_I32_u256'(t: Table int (int), k: $aa_i32_I32): int {
    GetTable(t, $EncodeKey'$aa_i32_I32'(k))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `(u64,vec'address')`

function $IsEqual'$1_table_with_length_TableWithLength'u64_vec'address'''(t1: Table int (Vec (int)), t2: Table int (Vec (int))): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_table_with_length_TableWithLength'u64_vec'address'''(t: Table int (Vec (int))): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'vec'address''(GetTable(t, i)))
}
procedure {:inline 2} $1_table_with_length_new'u64_vec'address''() returns (v: Table int (Vec (int))) {
    v := EmptyTable();
}
procedure {:inline 2} $1_table_with_length_destroy_empty'u64_vec'address''(t: Table int (Vec (int))) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_table_with_length_length'u64_vec'address''(t: (Table int (Vec (int)))) returns (l: int) {
    l := LenTable(t);
}
procedure {:inline 2} $1_table_with_length_empty'u64_vec'address''(t: (Table int (Vec (int)))) returns (r: bool) {
    r := LenTable(t) == 0;
}
procedure {:inline 2} $1_table_with_length_contains'u64_vec'address''(t: (Table int (Vec (int))), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'u64'(k));
}
procedure {:inline 2} $1_table_with_length_add'u64_vec'address''(m: $Mutation (Table int (Vec (int))), k: int, v: Vec (int)) returns (m': $Mutation(Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_with_length_upsert'u64_vec'address''(m: $Mutation (Table int (Vec (int))), k: int, v: Vec (int)) returns (m': $Mutation(Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, UpdateTable(t, enc_k, v));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_with_length_remove'u64_vec'address''(m: $Mutation (Table int (Vec (int))), k: int)
returns (v: Vec (int), m': $Mutation(Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_table_with_length_borrow'u64_vec'address''(t: Table int (Vec (int)), k: int) returns (v: Vec (int)) {
    var enc_k: int;
    enc_k := $EncodeKey'u64'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'u64'(k));
    }
}
procedure {:inline 2} $1_table_with_length_borrow_mut'u64_vec'address''(m: $Mutation (Table int (Vec (int))), k: int)
returns (dst: $Mutation (Vec (int)), m': $Mutation (Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
procedure {:inline 2} $1_table_with_length_borrow_mut_with_default'u64_vec'address''(m: $Mutation (Table int (Vec (int))), k: int, default: Vec (int))
returns (dst: $Mutation (Vec (int)), m': $Mutation (Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    var t': Table int (Vec (int));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, AddTable(t, enc_k, default));
        t' := $Dereference(m');
        dst := $Mutation(m'->l, ExtendVec(m'->p, enc_k), GetTable(t', enc_k));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_table_with_length_spec_len'u64_vec'address''(t: (Table int (Vec (int)))): int {
    LenTable(t)
}
function {:inline} $1_table_with_length_spec_contains'u64_vec'address''(t: (Table int (Vec (int))), k: int): bool {
    ContainsTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_table_with_length_spec_set'u64_vec'address''(t: Table int (Vec (int)), k: int, v: Vec (int)): Table int (Vec (int)) {
    (var enc_k := $EncodeKey'u64'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_table_with_length_spec_remove'u64_vec'address''(t: Table int (Vec (int)), k: int): Table int (Vec (int)) {
    RemoveTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_table_with_length_spec_get'u64_vec'address''(t: Table int (Vec (int)), k: int): Vec (int) {
    GetTable(t, $EncodeKey'u64'(k))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `(u64,vec'#0')`

function $IsEqual'$1_table_with_length_TableWithLength'u64_vec'#0'''(t1: Table int (Vec (#0)), t2: Table int (Vec (#0))): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_table_with_length_TableWithLength'u64_vec'#0'''(t: Table int (Vec (#0))): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'vec'#0''(GetTable(t, i)))
}
procedure {:inline 2} $1_table_with_length_new'u64_vec'#0''() returns (v: Table int (Vec (#0))) {
    v := EmptyTable();
}
procedure {:inline 2} $1_table_with_length_destroy_empty'u64_vec'#0''(t: Table int (Vec (#0))) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_table_with_length_length'u64_vec'#0''(t: (Table int (Vec (#0)))) returns (l: int) {
    l := LenTable(t);
}
procedure {:inline 2} $1_table_with_length_empty'u64_vec'#0''(t: (Table int (Vec (#0)))) returns (r: bool) {
    r := LenTable(t) == 0;
}
procedure {:inline 2} $1_table_with_length_contains'u64_vec'#0''(t: (Table int (Vec (#0))), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'u64'(k));
}
procedure {:inline 2} $1_table_with_length_add'u64_vec'#0''(m: $Mutation (Table int (Vec (#0))), k: int, v: Vec (#0)) returns (m': $Mutation(Table int (Vec (#0)))) {
    var enc_k: int;
    var t: Table int (Vec (#0));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_with_length_upsert'u64_vec'#0''(m: $Mutation (Table int (Vec (#0))), k: int, v: Vec (#0)) returns (m': $Mutation(Table int (Vec (#0)))) {
    var enc_k: int;
    var t: Table int (Vec (#0));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, UpdateTable(t, enc_k, v));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_with_length_remove'u64_vec'#0''(m: $Mutation (Table int (Vec (#0))), k: int)
returns (v: Vec (#0), m': $Mutation(Table int (Vec (#0)))) {
    var enc_k: int;
    var t: Table int (Vec (#0));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_table_with_length_borrow'u64_vec'#0''(t: Table int (Vec (#0)), k: int) returns (v: Vec (#0)) {
    var enc_k: int;
    enc_k := $EncodeKey'u64'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'u64'(k));
    }
}
procedure {:inline 2} $1_table_with_length_borrow_mut'u64_vec'#0''(m: $Mutation (Table int (Vec (#0))), k: int)
returns (dst: $Mutation (Vec (#0)), m': $Mutation (Table int (Vec (#0)))) {
    var enc_k: int;
    var t: Table int (Vec (#0));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
procedure {:inline 2} $1_table_with_length_borrow_mut_with_default'u64_vec'#0''(m: $Mutation (Table int (Vec (#0))), k: int, default: Vec (#0))
returns (dst: $Mutation (Vec (#0)), m': $Mutation (Table int (Vec (#0)))) {
    var enc_k: int;
    var t: Table int (Vec (#0));
    var t': Table int (Vec (#0));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, AddTable(t, enc_k, default));
        t' := $Dereference(m');
        dst := $Mutation(m'->l, ExtendVec(m'->p, enc_k), GetTable(t', enc_k));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_table_with_length_spec_len'u64_vec'#0''(t: (Table int (Vec (#0)))): int {
    LenTable(t)
}
function {:inline} $1_table_with_length_spec_contains'u64_vec'#0''(t: (Table int (Vec (#0))), k: int): bool {
    ContainsTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_table_with_length_spec_set'u64_vec'#0''(t: Table int (Vec (#0)), k: int, v: Vec (#0)): Table int (Vec (#0)) {
    (var enc_k := $EncodeKey'u64'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_table_with_length_spec_remove'u64_vec'#0''(t: Table int (Vec (#0)), k: int): Table int (Vec (#0)) {
    RemoveTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_table_with_length_spec_get'u64_vec'#0''(t: Table int (Vec (#0)), k: int): Vec (#0) {
    GetTable(t, $EncodeKey'u64'(k))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `($aa_i32_I32,$aa_tick_TickInfo)`

function $IsEqual'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(t1: Table int ($aa_tick_TickInfo), t2: Table int ($aa_tick_TickInfo)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(t: Table int ($aa_tick_TickInfo)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'$aa_tick_TickInfo'(GetTable(t, i)))
}
procedure {:inline 2} $1_smart_table_new'$aa_i32_I32_$aa_tick_TickInfo'() returns (v: Table int ($aa_tick_TickInfo)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_smart_table_destroy_empty'$aa_i32_I32_$aa_tick_TickInfo'(t: Table int ($aa_tick_TickInfo)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_smart_table_length'$aa_i32_I32_$aa_tick_TickInfo'(t: (Table int ($aa_tick_TickInfo))) returns (l: int) {
    l := LenTable(t);
}
procedure {:inline 2} $1_smart_table_contains'$aa_i32_I32_$aa_tick_TickInfo'(t: (Table int ($aa_tick_TickInfo)), k: $aa_i32_I32) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'$aa_i32_I32'(k));
}
procedure {:inline 2} $1_smart_table_add'$aa_i32_I32_$aa_tick_TickInfo'(m: $Mutation (Table int ($aa_tick_TickInfo)), k: $aa_i32_I32, v: $aa_tick_TickInfo) returns (m': $Mutation(Table int ($aa_tick_TickInfo))) {
    var enc_k: int;
    var t: Table int ($aa_tick_TickInfo);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_smart_table_upsert'$aa_i32_I32_$aa_tick_TickInfo'(m: $Mutation (Table int ($aa_tick_TickInfo)), k: $aa_i32_I32, v: $aa_tick_TickInfo) returns (m': $Mutation(Table int ($aa_tick_TickInfo))) {
    var enc_k: int;
    var t: Table int ($aa_tick_TickInfo);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, UpdateTable(t, enc_k, v));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_smart_table_remove'$aa_i32_I32_$aa_tick_TickInfo'(m: $Mutation (Table int ($aa_tick_TickInfo)), k: $aa_i32_I32)
returns (v: $aa_tick_TickInfo, m': $Mutation(Table int ($aa_tick_TickInfo))) {
    var enc_k: int;
    var t: Table int ($aa_tick_TickInfo);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_smart_table_borrow'$aa_i32_I32_$aa_tick_TickInfo'(t: Table int ($aa_tick_TickInfo), k: $aa_i32_I32) returns (v: $aa_tick_TickInfo) {
    var enc_k: int;
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'$aa_i32_I32'(k));
    }
}
procedure {:inline 2} $1_smart_table_borrow_mut'$aa_i32_I32_$aa_tick_TickInfo'(m: $Mutation (Table int ($aa_tick_TickInfo)), k: $aa_i32_I32)
returns (dst: $Mutation ($aa_tick_TickInfo), m': $Mutation (Table int ($aa_tick_TickInfo))) {
    var enc_k: int;
    var t: Table int ($aa_tick_TickInfo);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
procedure {:inline 2} $1_smart_table_borrow_mut_with_default'$aa_i32_I32_$aa_tick_TickInfo'(m: $Mutation (Table int ($aa_tick_TickInfo)), k: $aa_i32_I32, default: $aa_tick_TickInfo)
returns (dst: $Mutation ($aa_tick_TickInfo), m': $Mutation (Table int ($aa_tick_TickInfo))) {
    var enc_k: int;
    var t: Table int ($aa_tick_TickInfo);
    var t': Table int ($aa_tick_TickInfo);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, AddTable(t, enc_k, default));
        t' := $Dereference(m');
        dst := $Mutation(m'->l, ExtendVec(m'->p, enc_k), GetTable(t', enc_k));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_smart_table_spec_len'$aa_i32_I32_$aa_tick_TickInfo'(t: (Table int ($aa_tick_TickInfo))): int {
    LenTable(t)
}
function {:inline} $1_smart_table_spec_contains'$aa_i32_I32_$aa_tick_TickInfo'(t: (Table int ($aa_tick_TickInfo)), k: $aa_i32_I32): bool {
    ContainsTable(t, $EncodeKey'$aa_i32_I32'(k))
}
function {:inline} $1_smart_table_spec_set'$aa_i32_I32_$aa_tick_TickInfo'(t: Table int ($aa_tick_TickInfo), k: $aa_i32_I32, v: $aa_tick_TickInfo): Table int ($aa_tick_TickInfo) {
    (var enc_k := $EncodeKey'$aa_i32_I32'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_smart_table_spec_remove'$aa_i32_I32_$aa_tick_TickInfo'(t: Table int ($aa_tick_TickInfo), k: $aa_i32_I32): Table int ($aa_tick_TickInfo) {
    RemoveTable(t, $EncodeKey'$aa_i32_I32'(k))
}
function {:inline} $1_smart_table_spec_get'$aa_i32_I32_$aa_tick_TickInfo'(t: Table int ($aa_tick_TickInfo), k: $aa_i32_I32): $aa_tick_TickInfo {
    GetTable(t, $EncodeKey'$aa_i32_I32'(k))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `($aa_i32_I32,bv256)`

function $IsEqual'$1_table_Table'$aa_i32_I32_bv256''(t1: Table int (bv256), t2: Table int (bv256)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_table_Table'$aa_i32_I32_bv256''(t: Table int (bv256)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'bv256'(GetTable(t, i)))
}
procedure {:inline 2} $1_table_new'$aa_i32_I32_bv256'() returns (v: Table int (bv256)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_table_destroy_known_empty_unsafe'$aa_i32_I32_bv256'(t: Table int (bv256)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_table_contains'$aa_i32_I32_bv256'(t: (Table int (bv256)), k: $aa_i32_I32) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'$aa_i32_I32'(k));
}
procedure {:inline 2} $1_table_add'$aa_i32_I32_bv256'(m: $Mutation (Table int (bv256)), k: $aa_i32_I32, v: bv256) returns (m': $Mutation(Table int (bv256))) {
    var enc_k: int;
    var t: Table int (bv256);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_upsert'$aa_i32_I32_bv256'(m: $Mutation (Table int (bv256)), k: $aa_i32_I32, v: bv256) returns (m': $Mutation(Table int (bv256))) {
    var enc_k: int;
    var t: Table int (bv256);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, UpdateTable(t, enc_k, v));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_remove'$aa_i32_I32_bv256'(m: $Mutation (Table int (bv256)), k: $aa_i32_I32)
returns (v: bv256, m': $Mutation(Table int (bv256))) {
    var enc_k: int;
    var t: Table int (bv256);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_table_borrow'$aa_i32_I32_bv256'(t: Table int (bv256), k: $aa_i32_I32) returns (v: bv256) {
    var enc_k: int;
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'$aa_i32_I32'(k));
    }
}
procedure {:inline 2} $1_table_borrow_mut'$aa_i32_I32_bv256'(m: $Mutation (Table int (bv256)), k: $aa_i32_I32)
returns (dst: $Mutation (bv256), m': $Mutation (Table int (bv256))) {
    var enc_k: int;
    var t: Table int (bv256);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
procedure {:inline 2} $1_table_borrow_mut_with_default'$aa_i32_I32_bv256'(m: $Mutation (Table int (bv256)), k: $aa_i32_I32, default: bv256)
returns (dst: $Mutation (bv256), m': $Mutation (Table int (bv256))) {
    var enc_k: int;
    var t: Table int (bv256);
    var t': Table int (bv256);
    enc_k := $EncodeKey'$aa_i32_I32'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, AddTable(t, enc_k, default));
        t' := $Dereference(m');
        dst := $Mutation(m'->l, ExtendVec(m'->p, enc_k), GetTable(t', enc_k));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_table_spec_contains'$aa_i32_I32_bv256'(t: (Table int (bv256)), k: $aa_i32_I32): bool {
    ContainsTable(t, $EncodeKey'$aa_i32_I32'(k))
}
function {:inline} $1_table_spec_set'$aa_i32_I32_bv256'(t: Table int (bv256), k: $aa_i32_I32, v: bv256): Table int (bv256) {
    (var enc_k := $EncodeKey'$aa_i32_I32'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_table_spec_remove'$aa_i32_I32_bv256'(t: Table int (bv256), k: $aa_i32_I32): Table int (bv256) {
    RemoveTable(t, $EncodeKey'$aa_i32_I32'(k))
}
function {:inline} $1_table_spec_get'$aa_i32_I32_bv256'(t: Table int (bv256), k: $aa_i32_I32): bv256 {
    GetTable(t, $EncodeKey'$aa_i32_I32'(k))
}



// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

datatype $signer {
    $signer($addr: int),
    $permissioned_signer($addr: int, $permission_addr: int)
}

function {:inline} $IsValid'signer'(s: $signer): bool {
    if s is $signer then
        $IsValid'address'(s->$addr)
    else
        $IsValid'address'(s->$addr) &&
        $IsValid'address'(s->$permission_addr)
}

function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    if s1 is $signer && s2 is $signer then
        s1 == s2
    else if s1 is $permissioned_signer && s2 is $permissioned_signer then
        s1 == s2
    else
        false
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := signer->$addr;
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    signer->$addr
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}

// ============================================================================================
// Type Reflection on Type Parameters

datatype $TypeParamInfo {
    $TypeParamBool(),
    $TypeParamU8(),
    $TypeParamU16(),
    $TypeParamU32(),
    $TypeParamU64(),
    $TypeParamU128(),
    $TypeParamU256(),
    $TypeParamAddress(),
    $TypeParamSigner(),
    $TypeParamVector(e: $TypeParamInfo),
    $TypeParamStruct(a: int, m: Vec int, s: Vec int)
}



//==================================
// Begin Translation

function $TypeName(t: $TypeParamInfo): Vec int;
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamBool ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)) ==> t is $TypeParamBool);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU8 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)) ==> t is $TypeParamU8);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU16 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)) ==> t is $TypeParamU16);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU32 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)) ==> t is $TypeParamU32);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU64 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)) ==> t is $TypeParamU64);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU128 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)) ==> t is $TypeParamU128);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU256 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)) ==> t is $TypeParamU256);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamAddress ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)) ==> t is $TypeParamAddress);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamSigner ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)) ==> t is $TypeParamSigner);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamVector ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7), $TypeName(t->e)), Vec(DefaultVecMap()[0 := 62], 1))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} ($IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7)) && $IsSuffix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 62], 1))) ==> t is $TypeParamVector);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamStruct ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 48][1 := 120], 2), MakeVec1(t->a)), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->m), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->s)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 48][1 := 120], 2)) ==> t is $TypeParamVector);


// Given Types for Type Parameters

type #0;
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }
var #0_info: $TypeParamInfo;
var #0_$memory: $Memory #0;

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'bool'(b1), $1_from_bcs_deserializable'bool'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u8>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u8'(b1), $1_from_bcs_deserializable'u8'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u32>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u32'(b1), $1_from_bcs_deserializable'u32'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u64'(b1), $1_from_bcs_deserializable'u64'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u128'(b1), $1_from_bcs_deserializable'u128'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u256'(b1), $1_from_bcs_deserializable'u256'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'address'(b1), $1_from_bcs_deserializable'address'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u8''(b1), $1_from_bcs_deserializable'vec'u8''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u64''(b1), $1_from_bcs_deserializable'vec'u64''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u128''(b1), $1_from_bcs_deserializable'vec'u128''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'address''(b1), $1_from_bcs_deserializable'vec'address''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<0x1::fungible_asset::FungibleAsset>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_fungible_asset_FungibleAsset''(b1), $1_from_bcs_deserializable'vec'$1_fungible_asset_FungibleAsset''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<0x1::big_vector::BigVector<address>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_big_vector_BigVector'address'''(b1), $1_from_bcs_deserializable'vec'$1_big_vector_BigVector'address'''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<0xaa::rewarder::Rewarder>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$aa_rewarder_Rewarder''(b1), $1_from_bcs_deserializable'vec'$aa_rewarder_Rewarder''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'#0''(b1), $1_from_bcs_deserializable'vec'#0''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::option::Option<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'u64''(b1), $1_from_bcs_deserializable'$1_option_Option'u64''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::option::Option<0x1::fungible_asset::FungibleAsset>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'$1_fungible_asset_FungibleAsset''(b1), $1_from_bcs_deserializable'$1_option_Option'$1_fungible_asset_FungibleAsset''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::option::Option<0x1::big_vector::BigVector<address>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'$1_big_vector_BigVector'address'''(b1), $1_from_bcs_deserializable'$1_option_Option'$1_big_vector_BigVector'address'''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_string_String'(b1), $1_from_bcs_deserializable'$1_string_String'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::table::Table<0xaa::i32::I32, u256>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_table_Table'$aa_i32_I32_u256''(b1), $1_from_bcs_deserializable'$1_table_Table'$aa_i32_I32_u256''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::table_with_length::TableWithLength<u64, vector<address>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_table_with_length_TableWithLength'u64_vec'address'''(b1), $1_from_bcs_deserializable'$1_table_with_length_TableWithLength'u64_vec'address'''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::table_with_length::TableWithLength<u64, vector<#0>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_table_with_length_TableWithLength'u64_vec'#0'''(b1), $1_from_bcs_deserializable'$1_table_with_length_TableWithLength'u64_vec'#0'''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::permissioned_signer::GrantedPermissionHandles>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_permissioned_signer_GrantedPermissionHandles'(b1), $1_from_bcs_deserializable'$1_permissioned_signer_GrantedPermissionHandles'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::object::ExtendRef>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_object_ExtendRef'(b1), $1_from_bcs_deserializable'$1_object_ExtendRef'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::object::Object<0x1::fungible_asset::FungibleStore>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_object_Object'$1_fungible_asset_FungibleStore''(b1), $1_from_bcs_deserializable'$1_object_Object'$1_fungible_asset_FungibleStore''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::object::Object<0x1::fungible_asset::Metadata>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_object_Object'$1_fungible_asset_Metadata''(b1), $1_from_bcs_deserializable'$1_object_Object'$1_fungible_asset_Metadata''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::fungible_asset::TransferRef>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_fungible_asset_TransferRef'(b1), $1_from_bcs_deserializable'$1_fungible_asset_TransferRef'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::fungible_asset::BurnRef>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_fungible_asset_BurnRef'(b1), $1_from_bcs_deserializable'$1_fungible_asset_BurnRef'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::fungible_asset::FungibleAsset>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_fungible_asset_FungibleAsset'(b1), $1_from_bcs_deserializable'$1_fungible_asset_FungibleAsset'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::fungible_asset::MintRef>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_fungible_asset_MintRef'(b1), $1_from_bcs_deserializable'$1_fungible_asset_MintRef'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::smart_table::SmartTable<0xaa::i32::I32, 0xaa::tick::TickInfo>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(b1), $1_from_bcs_deserializable'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::big_vector::BigVector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_big_vector_BigVector'address''(b1), $1_from_bcs_deserializable'$1_big_vector_BigVector'address''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::smart_vector::SmartVector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_smart_vector_SmartVector'address''(b1), $1_from_bcs_deserializable'$1_smart_vector_SmartVector'address''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::i32::I32>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_i32_I32'(b1), $1_from_bcs_deserializable'$aa_i32_I32'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::i128::I128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_i128_I128'(b1), $1_from_bcs_deserializable'$aa_i128_I128'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::tick_bitmap::BitMap>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_tick_bitmap_BitMap'(b1), $1_from_bcs_deserializable'$aa_tick_bitmap_BitMap'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::rewarder::RewarderManager>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_rewarder_RewarderManager'(b1), $1_from_bcs_deserializable'$aa_rewarder_RewarderManager'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::position_blacklist::PositionBlackList>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_position_blacklist_PositionBlackList'(b1), $1_from_bcs_deserializable'$aa_position_blacklist_PositionBlackList'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::lp::LPTokenRefs>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_lp_LPTokenRefs'(b1), $1_from_bcs_deserializable'$aa_lp_LPTokenRefs'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::pool_v3::LiquidityPoolV3>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_pool_v3_LiquidityPoolV3'(b1), $1_from_bcs_deserializable'$aa_pool_v3_LiquidityPoolV3'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::pool_v3::ProtocolFees>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_pool_v3_ProtocolFees'(b1), $1_from_bcs_deserializable'$aa_pool_v3_ProtocolFees'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'#0'(b1), $1_from_bcs_deserializable'#0'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserialize'bool'(b1), $1_from_bcs_deserialize'bool'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u8>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u8'($1_from_bcs_deserialize'u8'(b1), $1_from_bcs_deserialize'u8'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u32>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u32'($1_from_bcs_deserialize'u32'(b1), $1_from_bcs_deserialize'u32'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u64'($1_from_bcs_deserialize'u64'(b1), $1_from_bcs_deserialize'u64'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u128'($1_from_bcs_deserialize'u128'(b1), $1_from_bcs_deserialize'u128'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u256'($1_from_bcs_deserialize'u256'(b1), $1_from_bcs_deserialize'u256'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'address'($1_from_bcs_deserialize'address'(b1), $1_from_bcs_deserialize'address'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u64''($1_from_bcs_deserialize'vec'u64''(b1), $1_from_bcs_deserialize'vec'u64''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u128''($1_from_bcs_deserialize'vec'u128''(b1), $1_from_bcs_deserialize'vec'u128''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'address''($1_from_bcs_deserialize'vec'address''(b1), $1_from_bcs_deserialize'vec'address''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<0x1::fungible_asset::FungibleAsset>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_fungible_asset_FungibleAsset''($1_from_bcs_deserialize'vec'$1_fungible_asset_FungibleAsset''(b1), $1_from_bcs_deserialize'vec'$1_fungible_asset_FungibleAsset''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<0x1::big_vector::BigVector<address>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_big_vector_BigVector'address'''($1_from_bcs_deserialize'vec'$1_big_vector_BigVector'address'''(b1), $1_from_bcs_deserialize'vec'$1_big_vector_BigVector'address'''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<0xaa::rewarder::Rewarder>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$aa_rewarder_Rewarder''($1_from_bcs_deserialize'vec'$aa_rewarder_Rewarder''(b1), $1_from_bcs_deserialize'vec'$aa_rewarder_Rewarder''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'#0''($1_from_bcs_deserialize'vec'#0''(b1), $1_from_bcs_deserialize'vec'#0''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::option::Option<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'u64''($1_from_bcs_deserialize'$1_option_Option'u64''(b1), $1_from_bcs_deserialize'$1_option_Option'u64''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::option::Option<0x1::fungible_asset::FungibleAsset>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'$1_fungible_asset_FungibleAsset''($1_from_bcs_deserialize'$1_option_Option'$1_fungible_asset_FungibleAsset''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_fungible_asset_FungibleAsset''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::option::Option<0x1::big_vector::BigVector<address>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'$1_big_vector_BigVector'address'''($1_from_bcs_deserialize'$1_option_Option'$1_big_vector_BigVector'address'''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_big_vector_BigVector'address'''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_string_String'($1_from_bcs_deserialize'$1_string_String'(b1), $1_from_bcs_deserialize'$1_string_String'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::table::Table<0xaa::i32::I32, u256>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_table_Table'$aa_i32_I32_u256''($1_from_bcs_deserialize'$1_table_Table'$aa_i32_I32_u256''(b1), $1_from_bcs_deserialize'$1_table_Table'$aa_i32_I32_u256''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::table_with_length::TableWithLength<u64, vector<address>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_table_with_length_TableWithLength'u64_vec'address'''($1_from_bcs_deserialize'$1_table_with_length_TableWithLength'u64_vec'address'''(b1), $1_from_bcs_deserialize'$1_table_with_length_TableWithLength'u64_vec'address'''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::table_with_length::TableWithLength<u64, vector<#0>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_table_with_length_TableWithLength'u64_vec'#0'''($1_from_bcs_deserialize'$1_table_with_length_TableWithLength'u64_vec'#0'''(b1), $1_from_bcs_deserialize'$1_table_with_length_TableWithLength'u64_vec'#0'''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::permissioned_signer::GrantedPermissionHandles>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_permissioned_signer_GrantedPermissionHandles'($1_from_bcs_deserialize'$1_permissioned_signer_GrantedPermissionHandles'(b1), $1_from_bcs_deserialize'$1_permissioned_signer_GrantedPermissionHandles'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::object::ExtendRef>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_object_ExtendRef'($1_from_bcs_deserialize'$1_object_ExtendRef'(b1), $1_from_bcs_deserialize'$1_object_ExtendRef'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::object::Object<0x1::fungible_asset::FungibleStore>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_object_Object'$1_fungible_asset_FungibleStore''($1_from_bcs_deserialize'$1_object_Object'$1_fungible_asset_FungibleStore''(b1), $1_from_bcs_deserialize'$1_object_Object'$1_fungible_asset_FungibleStore''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::object::Object<0x1::fungible_asset::Metadata>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_object_Object'$1_fungible_asset_Metadata''($1_from_bcs_deserialize'$1_object_Object'$1_fungible_asset_Metadata''(b1), $1_from_bcs_deserialize'$1_object_Object'$1_fungible_asset_Metadata''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::fungible_asset::TransferRef>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_fungible_asset_TransferRef'($1_from_bcs_deserialize'$1_fungible_asset_TransferRef'(b1), $1_from_bcs_deserialize'$1_fungible_asset_TransferRef'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::fungible_asset::BurnRef>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_fungible_asset_BurnRef'($1_from_bcs_deserialize'$1_fungible_asset_BurnRef'(b1), $1_from_bcs_deserialize'$1_fungible_asset_BurnRef'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::fungible_asset::FungibleAsset>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_fungible_asset_FungibleAsset'($1_from_bcs_deserialize'$1_fungible_asset_FungibleAsset'(b1), $1_from_bcs_deserialize'$1_fungible_asset_FungibleAsset'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::fungible_asset::MintRef>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_fungible_asset_MintRef'($1_from_bcs_deserialize'$1_fungible_asset_MintRef'(b1), $1_from_bcs_deserialize'$1_fungible_asset_MintRef'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::smart_table::SmartTable<0xaa::i32::I32, 0xaa::tick::TickInfo>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''($1_from_bcs_deserialize'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(b1), $1_from_bcs_deserialize'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::big_vector::BigVector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_big_vector_BigVector'address''($1_from_bcs_deserialize'$1_big_vector_BigVector'address''(b1), $1_from_bcs_deserialize'$1_big_vector_BigVector'address''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::smart_vector::SmartVector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_smart_vector_SmartVector'address''($1_from_bcs_deserialize'$1_smart_vector_SmartVector'address''(b1), $1_from_bcs_deserialize'$1_smart_vector_SmartVector'address''(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::i32::I32>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_i32_I32'($1_from_bcs_deserialize'$aa_i32_I32'(b1), $1_from_bcs_deserialize'$aa_i32_I32'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::i128::I128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_i128_I128'($1_from_bcs_deserialize'$aa_i128_I128'(b1), $1_from_bcs_deserialize'$aa_i128_I128'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::tick_bitmap::BitMap>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_tick_bitmap_BitMap'($1_from_bcs_deserialize'$aa_tick_bitmap_BitMap'(b1), $1_from_bcs_deserialize'$aa_tick_bitmap_BitMap'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::rewarder::RewarderManager>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_rewarder_RewarderManager'($1_from_bcs_deserialize'$aa_rewarder_RewarderManager'(b1), $1_from_bcs_deserialize'$aa_rewarder_RewarderManager'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::position_blacklist::PositionBlackList>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_position_blacklist_PositionBlackList'($1_from_bcs_deserialize'$aa_position_blacklist_PositionBlackList'(b1), $1_from_bcs_deserialize'$aa_position_blacklist_PositionBlackList'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::lp::LPTokenRefs>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_lp_LPTokenRefs'($1_from_bcs_deserialize'$aa_lp_LPTokenRefs'(b1), $1_from_bcs_deserialize'$aa_lp_LPTokenRefs'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::pool_v3::LiquidityPoolV3>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_pool_v3_LiquidityPoolV3'($1_from_bcs_deserialize'$aa_pool_v3_LiquidityPoolV3'(b1), $1_from_bcs_deserialize'$aa_pool_v3_LiquidityPoolV3'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::pool_v3::ProtocolFees>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_pool_v3_ProtocolFees'($1_from_bcs_deserialize'$aa_pool_v3_ProtocolFees'(b1), $1_from_bcs_deserialize'$aa_pool_v3_ProtocolFees'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/permissioned_signer.spec.move:5:9+288
axiom (forall a: $1_permissioned_signer_GrantedPermissionHandles :: $IsValid'$1_permissioned_signer_GrantedPermissionHandles'(a) ==> ((var $range_0 := $Range(0, LenVec(a->$active_handles)); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var i := $i_1;
((var $range_2 := $Range(0, LenVec(a->$active_handles)); (forall $i_3: int :: $InRange($range_2, $i_3) ==> (var j := $i_3;
((!$IsEqual'num'(i, j) ==> !$IsEqual'address'(ReadVec(a->$active_handles, i), ReadVec(a->$active_handles, j)))))))))))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:8:9+113
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_keccak256(b1), $1_aptos_hash_spec_keccak256(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:13:9+129
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_sha2_512_internal(b1), $1_aptos_hash_spec_sha2_512_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:18:9+129
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_sha3_512_internal(b1), $1_aptos_hash_spec_sha3_512_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:23:9+131
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_ripemd160_internal(b1), $1_aptos_hash_spec_ripemd160_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:28:9+135
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_blake2b_256_internal(b1), $1_aptos_hash_spec_blake2b_256_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:199:5+92
function {:inline} $1_vector_$is_empty'u64'(self: Vec (int)): bool {
    $IsEqual'u64'($1_vector_$length'u64'(self), 0)
}

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:34:10+78
function {:inline} $1_option_spec_none'$1_fungible_asset_FungibleAsset'(): $1_option_Option'$1_fungible_asset_FungibleAsset' {
    $1_option_Option'$1_fungible_asset_FungibleAsset'($EmptyVec'$1_fungible_asset_FungibleAsset'())
}

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:102:5+154
function {:inline} $1_option_$borrow'u64'(self: $1_option_Option'u64'): int {
    $1_vector_$borrow'u64'(self->$vec, 0)
}

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:61:5+101
function {:inline} $1_option_$is_none'u64'(self: $1_option_Option'u64'): bool {
    $1_vector_$is_empty'u64'(self->$vec)
}

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:74:5+102
function {:inline} $1_option_$is_some'u64'(self: $1_option_Option'u64'): bool {
    !$1_vector_$is_empty'u64'(self->$vec)
}

// struct option::Option<u64> at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:7:5+81
datatype $1_option_Option'u64' {
    $1_option_Option'u64'($vec: Vec (int))
}
function {:inline} $Update'$1_option_Option'u64''_vec(s: $1_option_Option'u64', x: Vec (int)): $1_option_Option'u64' {
    $1_option_Option'u64'(x)
}
function $IsValid'$1_option_Option'u64''(s: $1_option_Option'u64'): bool {
    $IsValid'vec'u64''(s->$vec)
}
function {:inline} $IsEqual'$1_option_Option'u64''(s1: $1_option_Option'u64', s2: $1_option_Option'u64'): bool {
    $IsEqual'vec'u64''(s1->$vec, s2->$vec)}

// struct option::Option<0x1::fungible_asset::FungibleAsset> at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:7:5+81
datatype $1_option_Option'$1_fungible_asset_FungibleAsset' {
    $1_option_Option'$1_fungible_asset_FungibleAsset'($vec: Vec ($1_fungible_asset_FungibleAsset))
}
function {:inline} $Update'$1_option_Option'$1_fungible_asset_FungibleAsset''_vec(s: $1_option_Option'$1_fungible_asset_FungibleAsset', x: Vec ($1_fungible_asset_FungibleAsset)): $1_option_Option'$1_fungible_asset_FungibleAsset' {
    $1_option_Option'$1_fungible_asset_FungibleAsset'(x)
}
function $IsValid'$1_option_Option'$1_fungible_asset_FungibleAsset''(s: $1_option_Option'$1_fungible_asset_FungibleAsset'): bool {
    $IsValid'vec'$1_fungible_asset_FungibleAsset''(s->$vec)
}
function {:inline} $IsEqual'$1_option_Option'$1_fungible_asset_FungibleAsset''(s1: $1_option_Option'$1_fungible_asset_FungibleAsset', s2: $1_option_Option'$1_fungible_asset_FungibleAsset'): bool {
    $IsEqual'vec'$1_fungible_asset_FungibleAsset''(s1->$vec, s2->$vec)}

// struct option::Option<0x1::big_vector::BigVector<address>> at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:7:5+81
datatype $1_option_Option'$1_big_vector_BigVector'address'' {
    $1_option_Option'$1_big_vector_BigVector'address''($vec: Vec ($1_big_vector_BigVector'address'))
}
function {:inline} $Update'$1_option_Option'$1_big_vector_BigVector'address'''_vec(s: $1_option_Option'$1_big_vector_BigVector'address'', x: Vec ($1_big_vector_BigVector'address')): $1_option_Option'$1_big_vector_BigVector'address'' {
    $1_option_Option'$1_big_vector_BigVector'address''(x)
}
function $IsValid'$1_option_Option'$1_big_vector_BigVector'address'''(s: $1_option_Option'$1_big_vector_BigVector'address''): bool {
    $IsValid'vec'$1_big_vector_BigVector'address'''(s->$vec)
}
function {:inline} $IsEqual'$1_option_Option'$1_big_vector_BigVector'address'''(s1: $1_option_Option'$1_big_vector_BigVector'address'', s2: $1_option_Option'$1_big_vector_BigVector'address''): bool {
    $IsEqual'vec'$1_big_vector_BigVector'address'''(s1->$vec, s2->$vec)}

// struct string::String at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:13:5+70
datatype $1_string_String {
    $1_string_String($bytes: Vec (int))
}
function {:inline} $Update'$1_string_String'_bytes(s: $1_string_String, x: Vec (int)): $1_string_String {
    $1_string_String(x)
}
function $IsValid'$1_string_String'(s: $1_string_String): bool {
    $IsValid'vec'u8''(s->$bytes)
}
function {:inline} $IsEqual'$1_string_String'(s1: $1_string_String, s2: $1_string_String): bool {
    $IsEqual'vec'u8''(s1->$bytes, s2->$bytes)}

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'bool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'bool'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u8'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u8'(bytes);
$IsValid'u8'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u32'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u32'(bytes);
$IsValid'u32'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u64'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u64'(bytes);
$IsValid'u64'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u128'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u128'(bytes);
$IsValid'u128'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u256'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u256'(bytes);
$IsValid'u256'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'address'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'address'(bytes);
$IsValid'address'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u8''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u8''(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u64''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u64''(bytes);
$IsValid'vec'u64''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u128''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u128''(bytes);
$IsValid'vec'u128''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'address''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'address''(bytes);
$IsValid'vec'address''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'$1_fungible_asset_FungibleAsset''(bytes: Vec (int)): Vec ($1_fungible_asset_FungibleAsset);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_fungible_asset_FungibleAsset''(bytes);
$IsValid'vec'$1_fungible_asset_FungibleAsset''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'$1_big_vector_BigVector'address'''(bytes: Vec (int)): Vec ($1_big_vector_BigVector'address');
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_big_vector_BigVector'address'''(bytes);
$IsValid'vec'$1_big_vector_BigVector'address'''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'$aa_rewarder_Rewarder''(bytes: Vec (int)): Vec ($aa_rewarder_Rewarder);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$aa_rewarder_Rewarder''(bytes);
$IsValid'vec'$aa_rewarder_Rewarder''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'#0''(bytes: Vec (int)): Vec (#0);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'#0''(bytes);
$IsValid'vec'#0''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'u64''(bytes: Vec (int)): $1_option_Option'u64';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'u64''(bytes);
$IsValid'$1_option_Option'u64''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'$1_fungible_asset_FungibleAsset''(bytes: Vec (int)): $1_option_Option'$1_fungible_asset_FungibleAsset';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'$1_fungible_asset_FungibleAsset''(bytes);
$IsValid'$1_option_Option'$1_fungible_asset_FungibleAsset''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'$1_big_vector_BigVector'address'''(bytes: Vec (int)): $1_option_Option'$1_big_vector_BigVector'address'';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'$1_big_vector_BigVector'address'''(bytes);
$IsValid'$1_option_Option'$1_big_vector_BigVector'address'''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_string_String'(bytes: Vec (int)): $1_string_String;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_string_String'(bytes);
$IsValid'$1_string_String'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_table_Table'$aa_i32_I32_u256''(bytes: Vec (int)): Table int (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_table_Table'$aa_i32_I32_u256''(bytes);
$IsValid'$1_table_Table'$aa_i32_I32_u256''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_table_with_length_TableWithLength'u64_vec'address'''(bytes: Vec (int)): Table int (Vec (int));
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_table_with_length_TableWithLength'u64_vec'address'''(bytes);
$IsValid'$1_table_with_length_TableWithLength'u64_vec'address'''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_table_with_length_TableWithLength'u64_vec'#0'''(bytes: Vec (int)): Table int (Vec (#0));
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_table_with_length_TableWithLength'u64_vec'#0'''(bytes);
$IsValid'$1_table_with_length_TableWithLength'u64_vec'#0'''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_permissioned_signer_GrantedPermissionHandles'(bytes: Vec (int)): $1_permissioned_signer_GrantedPermissionHandles;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_permissioned_signer_GrantedPermissionHandles'(bytes);
$IsValid'$1_permissioned_signer_GrantedPermissionHandles'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_object_ExtendRef'(bytes: Vec (int)): $1_object_ExtendRef;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_object_ExtendRef'(bytes);
$IsValid'$1_object_ExtendRef'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_object_Object'$1_fungible_asset_FungibleStore''(bytes: Vec (int)): $1_object_Object'$1_fungible_asset_FungibleStore';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_object_Object'$1_fungible_asset_FungibleStore''(bytes);
$IsValid'$1_object_Object'$1_fungible_asset_FungibleStore''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_object_Object'$1_fungible_asset_Metadata''(bytes: Vec (int)): $1_object_Object'$1_fungible_asset_Metadata';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_object_Object'$1_fungible_asset_Metadata''(bytes);
$IsValid'$1_object_Object'$1_fungible_asset_Metadata''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_fungible_asset_TransferRef'(bytes: Vec (int)): $1_fungible_asset_TransferRef;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_fungible_asset_TransferRef'(bytes);
$IsValid'$1_fungible_asset_TransferRef'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_fungible_asset_BurnRef'(bytes: Vec (int)): $1_fungible_asset_BurnRef;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_fungible_asset_BurnRef'(bytes);
$IsValid'$1_fungible_asset_BurnRef'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_fungible_asset_FungibleAsset'(bytes: Vec (int)): $1_fungible_asset_FungibleAsset;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_fungible_asset_FungibleAsset'(bytes);
$IsValid'$1_fungible_asset_FungibleAsset'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_fungible_asset_MintRef'(bytes: Vec (int)): $1_fungible_asset_MintRef;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_fungible_asset_MintRef'(bytes);
$IsValid'$1_fungible_asset_MintRef'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(bytes: Vec (int)): Table int ($aa_tick_TickInfo);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(bytes);
$IsValid'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_big_vector_BigVector'address''(bytes: Vec (int)): $1_big_vector_BigVector'address';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_big_vector_BigVector'address''(bytes);
$IsValid'$1_big_vector_BigVector'address''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_smart_vector_SmartVector'address''(bytes: Vec (int)): $1_smart_vector_SmartVector'address';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_smart_vector_SmartVector'address''(bytes);
$IsValid'$1_smart_vector_SmartVector'address''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_i32_I32'(bytes: Vec (int)): $aa_i32_I32;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_i32_I32'(bytes);
$IsValid'$aa_i32_I32'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_i128_I128'(bytes: Vec (int)): $aa_i128_I128;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_i128_I128'(bytes);
$IsValid'$aa_i128_I128'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_tick_bitmap_BitMap'(bytes: Vec (int)): $aa_tick_bitmap_BitMap;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_tick_bitmap_BitMap'(bytes);
$IsValid'$aa_tick_bitmap_BitMap'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_rewarder_RewarderManager'(bytes: Vec (int)): $aa_rewarder_RewarderManager;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_rewarder_RewarderManager'(bytes);
$IsValid'$aa_rewarder_RewarderManager'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_position_blacklist_PositionBlackList'(bytes: Vec (int)): $aa_position_blacklist_PositionBlackList;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_position_blacklist_PositionBlackList'(bytes);
$IsValid'$aa_position_blacklist_PositionBlackList'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_lp_LPTokenRefs'(bytes: Vec (int)): $aa_lp_LPTokenRefs;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_lp_LPTokenRefs'(bytes);
$IsValid'$aa_lp_LPTokenRefs'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_pool_v3_LiquidityPoolV3'(bytes: Vec (int)): $aa_pool_v3_LiquidityPoolV3;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_pool_v3_LiquidityPoolV3'(bytes);
$IsValid'$aa_pool_v3_LiquidityPoolV3'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_pool_v3_ProtocolFees'(bytes: Vec (int)): $aa_pool_v3_ProtocolFees;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_pool_v3_ProtocolFees'(bytes);
$IsValid'$aa_pool_v3_ProtocolFees'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'#0'(bytes: Vec (int)): #0;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'#0'(bytes);
$IsValid'#0'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'bool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'bool'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u8'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u8'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u32'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u32'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u64'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u64'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u128'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u128'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u256'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u256'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'address'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'address'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u8''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u8''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u64''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u64''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u128''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u128''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'address''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'address''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'$1_fungible_asset_FungibleAsset''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_fungible_asset_FungibleAsset''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'$1_big_vector_BigVector'address'''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_big_vector_BigVector'address'''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'$aa_rewarder_Rewarder''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$aa_rewarder_Rewarder''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'#0''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'#0''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'u64''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'u64''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'$1_fungible_asset_FungibleAsset''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'$1_fungible_asset_FungibleAsset''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'$1_big_vector_BigVector'address'''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'$1_big_vector_BigVector'address'''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_string_String'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_string_String'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_table_Table'$aa_i32_I32_u256''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_table_Table'$aa_i32_I32_u256''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_table_with_length_TableWithLength'u64_vec'address'''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_table_with_length_TableWithLength'u64_vec'address'''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_table_with_length_TableWithLength'u64_vec'#0'''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_table_with_length_TableWithLength'u64_vec'#0'''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_permissioned_signer_GrantedPermissionHandles'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_permissioned_signer_GrantedPermissionHandles'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_object_ExtendRef'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_object_ExtendRef'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_object_Object'$1_fungible_asset_FungibleStore''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_object_Object'$1_fungible_asset_FungibleStore''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_object_Object'$1_fungible_asset_Metadata''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_object_Object'$1_fungible_asset_Metadata''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_fungible_asset_TransferRef'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_fungible_asset_TransferRef'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_fungible_asset_BurnRef'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_fungible_asset_BurnRef'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_fungible_asset_FungibleAsset'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_fungible_asset_FungibleAsset'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_fungible_asset_MintRef'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_fungible_asset_MintRef'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_big_vector_BigVector'address''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_big_vector_BigVector'address''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_smart_vector_SmartVector'address''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_smart_vector_SmartVector'address''(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_i32_I32'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_i32_I32'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_i128_I128'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_i128_I128'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_tick_bitmap_BitMap'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_tick_bitmap_BitMap'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_rewarder_RewarderManager'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_rewarder_RewarderManager'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_position_blacklist_PositionBlackList'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_position_blacklist_PositionBlackList'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_lp_LPTokenRefs'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_lp_LPTokenRefs'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_pool_v3_LiquidityPoolV3'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_pool_v3_LiquidityPoolV3'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_pool_v3_ProtocolFees'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_pool_v3_ProtocolFees'(bytes);
$IsValid'bool'($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'#0'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'#0'(bytes);
$IsValid'bool'($$res)));

// struct permissioned_signer::GrantedPermissionHandles at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/permissioned_signer.move:64:5+188
datatype $1_permissioned_signer_GrantedPermissionHandles {
    $1_permissioned_signer_GrantedPermissionHandles($active_handles: Vec (int))
}
function {:inline} $Update'$1_permissioned_signer_GrantedPermissionHandles'_active_handles(s: $1_permissioned_signer_GrantedPermissionHandles, x: Vec (int)): $1_permissioned_signer_GrantedPermissionHandles {
    $1_permissioned_signer_GrantedPermissionHandles(x)
}
function $IsValid'$1_permissioned_signer_GrantedPermissionHandles'(s: $1_permissioned_signer_GrantedPermissionHandles): bool {
    $IsValid'vec'address''(s->$active_handles)
}
function {:inline} $IsEqual'$1_permissioned_signer_GrantedPermissionHandles'(s1: $1_permissioned_signer_GrantedPermissionHandles, s2: $1_permissioned_signer_GrantedPermissionHandles): bool {
    $IsEqual'vec'address''(s1->$active_handles, s2->$active_handles)}
var $1_permissioned_signer_GrantedPermissionHandles_$memory: $Memory $1_permissioned_signer_GrantedPermissionHandles;

// struct object::ExtendRef at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/object.move:148:5+63
datatype $1_object_ExtendRef {
    $1_object_ExtendRef($self: int)
}
function {:inline} $Update'$1_object_ExtendRef'_self(s: $1_object_ExtendRef, x: int): $1_object_ExtendRef {
    $1_object_ExtendRef(x)
}
function $IsValid'$1_object_ExtendRef'(s: $1_object_ExtendRef): bool {
    $IsValid'address'(s->$self)
}
function {:inline} $IsEqual'$1_object_ExtendRef'(s1: $1_object_ExtendRef, s2: $1_object_ExtendRef): bool {
    s1 == s2
}

// struct object::Object<0x1::fungible_asset::FungibleStore> at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/object.move:131:5+78
datatype $1_object_Object'$1_fungible_asset_FungibleStore' {
    $1_object_Object'$1_fungible_asset_FungibleStore'($inner: int)
}
function {:inline} $Update'$1_object_Object'$1_fungible_asset_FungibleStore''_inner(s: $1_object_Object'$1_fungible_asset_FungibleStore', x: int): $1_object_Object'$1_fungible_asset_FungibleStore' {
    $1_object_Object'$1_fungible_asset_FungibleStore'(x)
}
function $IsValid'$1_object_Object'$1_fungible_asset_FungibleStore''(s: $1_object_Object'$1_fungible_asset_FungibleStore'): bool {
    $IsValid'address'(s->$inner)
}
function {:inline} $IsEqual'$1_object_Object'$1_fungible_asset_FungibleStore''(s1: $1_object_Object'$1_fungible_asset_FungibleStore', s2: $1_object_Object'$1_fungible_asset_FungibleStore'): bool {
    s1 == s2
}

// struct object::Object<0x1::fungible_asset::Metadata> at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/object.move:131:5+78
datatype $1_object_Object'$1_fungible_asset_Metadata' {
    $1_object_Object'$1_fungible_asset_Metadata'($inner: int)
}
function {:inline} $Update'$1_object_Object'$1_fungible_asset_Metadata''_inner(s: $1_object_Object'$1_fungible_asset_Metadata', x: int): $1_object_Object'$1_fungible_asset_Metadata' {
    $1_object_Object'$1_fungible_asset_Metadata'(x)
}
function $IsValid'$1_object_Object'$1_fungible_asset_Metadata''(s: $1_object_Object'$1_fungible_asset_Metadata'): bool {
    $IsValid'address'(s->$inner)
}
function {:inline} $IsEqual'$1_object_Object'$1_fungible_asset_Metadata''(s1: $1_object_Object'$1_fungible_asset_Metadata', s2: $1_object_Object'$1_fungible_asset_Metadata'): bool {
    s1 == s2
}

// struct fungible_asset::TransferRef at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/fungible_asset.move:190:5+77
datatype $1_fungible_asset_TransferRef {
    $1_fungible_asset_TransferRef($metadata: $1_object_Object'$1_fungible_asset_Metadata')
}
function {:inline} $Update'$1_fungible_asset_TransferRef'_metadata(s: $1_fungible_asset_TransferRef, x: $1_object_Object'$1_fungible_asset_Metadata'): $1_fungible_asset_TransferRef {
    $1_fungible_asset_TransferRef(x)
}
function $IsValid'$1_fungible_asset_TransferRef'(s: $1_fungible_asset_TransferRef): bool {
    $IsValid'$1_object_Object'$1_fungible_asset_Metadata''(s->$metadata)
}
function {:inline} $IsEqual'$1_fungible_asset_TransferRef'(s1: $1_fungible_asset_TransferRef, s2: $1_fungible_asset_TransferRef): bool {
    s1 == s2
}

// struct fungible_asset::BurnRef at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/fungible_asset.move:205:5+73
datatype $1_fungible_asset_BurnRef {
    $1_fungible_asset_BurnRef($metadata: $1_object_Object'$1_fungible_asset_Metadata')
}
function {:inline} $Update'$1_fungible_asset_BurnRef'_metadata(s: $1_fungible_asset_BurnRef, x: $1_object_Object'$1_fungible_asset_Metadata'): $1_fungible_asset_BurnRef {
    $1_fungible_asset_BurnRef(x)
}
function $IsValid'$1_fungible_asset_BurnRef'(s: $1_fungible_asset_BurnRef): bool {
    $IsValid'$1_object_Object'$1_fungible_asset_Metadata''(s->$metadata)
}
function {:inline} $IsEqual'$1_fungible_asset_BurnRef'(s1: $1_fungible_asset_BurnRef, s2: $1_fungible_asset_BurnRef): bool {
    s1 == s2
}

// struct fungible_asset::FungibleAsset at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/fungible_asset.move:178:5+85
datatype $1_fungible_asset_FungibleAsset {
    $1_fungible_asset_FungibleAsset($metadata: $1_object_Object'$1_fungible_asset_Metadata', $amount: int)
}
function {:inline} $Update'$1_fungible_asset_FungibleAsset'_metadata(s: $1_fungible_asset_FungibleAsset, x: $1_object_Object'$1_fungible_asset_Metadata'): $1_fungible_asset_FungibleAsset {
    $1_fungible_asset_FungibleAsset(x, s->$amount)
}
function {:inline} $Update'$1_fungible_asset_FungibleAsset'_amount(s: $1_fungible_asset_FungibleAsset, x: int): $1_fungible_asset_FungibleAsset {
    $1_fungible_asset_FungibleAsset(s->$metadata, x)
}
function $IsValid'$1_fungible_asset_FungibleAsset'(s: $1_fungible_asset_FungibleAsset): bool {
    $IsValid'$1_object_Object'$1_fungible_asset_Metadata''(s->$metadata)
      && $IsValid'u64'(s->$amount)
}
function {:inline} $IsEqual'$1_fungible_asset_FungibleAsset'(s1: $1_fungible_asset_FungibleAsset, s2: $1_fungible_asset_FungibleAsset): bool {
    s1 == s2
}

// struct fungible_asset::FungibleStore at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/fungible_asset.move:148:5+324
datatype $1_fungible_asset_FungibleStore {
    $1_fungible_asset_FungibleStore($metadata: $1_object_Object'$1_fungible_asset_Metadata', $balance: int, $frozen: bool)
}
function {:inline} $Update'$1_fungible_asset_FungibleStore'_metadata(s: $1_fungible_asset_FungibleStore, x: $1_object_Object'$1_fungible_asset_Metadata'): $1_fungible_asset_FungibleStore {
    $1_fungible_asset_FungibleStore(x, s->$balance, s->$frozen)
}
function {:inline} $Update'$1_fungible_asset_FungibleStore'_balance(s: $1_fungible_asset_FungibleStore, x: int): $1_fungible_asset_FungibleStore {
    $1_fungible_asset_FungibleStore(s->$metadata, x, s->$frozen)
}
function {:inline} $Update'$1_fungible_asset_FungibleStore'_frozen(s: $1_fungible_asset_FungibleStore, x: bool): $1_fungible_asset_FungibleStore {
    $1_fungible_asset_FungibleStore(s->$metadata, s->$balance, x)
}
function $IsValid'$1_fungible_asset_FungibleStore'(s: $1_fungible_asset_FungibleStore): bool {
    $IsValid'$1_object_Object'$1_fungible_asset_Metadata''(s->$metadata)
      && $IsValid'u64'(s->$balance)
      && $IsValid'bool'(s->$frozen)
}
function {:inline} $IsEqual'$1_fungible_asset_FungibleStore'(s1: $1_fungible_asset_FungibleStore, s2: $1_fungible_asset_FungibleStore): bool {
    s1 == s2
}
var $1_fungible_asset_FungibleStore_$memory: $Memory $1_fungible_asset_FungibleStore;

// struct fungible_asset::Metadata at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/fungible_asset.move:124:5+797
datatype $1_fungible_asset_Metadata {
    $1_fungible_asset_Metadata($name: $1_string_String, $symbol: $1_string_String, $decimals: int, $icon_uri: $1_string_String, $project_uri: $1_string_String)
}
function {:inline} $Update'$1_fungible_asset_Metadata'_name(s: $1_fungible_asset_Metadata, x: $1_string_String): $1_fungible_asset_Metadata {
    $1_fungible_asset_Metadata(x, s->$symbol, s->$decimals, s->$icon_uri, s->$project_uri)
}
function {:inline} $Update'$1_fungible_asset_Metadata'_symbol(s: $1_fungible_asset_Metadata, x: $1_string_String): $1_fungible_asset_Metadata {
    $1_fungible_asset_Metadata(s->$name, x, s->$decimals, s->$icon_uri, s->$project_uri)
}
function {:inline} $Update'$1_fungible_asset_Metadata'_decimals(s: $1_fungible_asset_Metadata, x: int): $1_fungible_asset_Metadata {
    $1_fungible_asset_Metadata(s->$name, s->$symbol, x, s->$icon_uri, s->$project_uri)
}
function {:inline} $Update'$1_fungible_asset_Metadata'_icon_uri(s: $1_fungible_asset_Metadata, x: $1_string_String): $1_fungible_asset_Metadata {
    $1_fungible_asset_Metadata(s->$name, s->$symbol, s->$decimals, x, s->$project_uri)
}
function {:inline} $Update'$1_fungible_asset_Metadata'_project_uri(s: $1_fungible_asset_Metadata, x: $1_string_String): $1_fungible_asset_Metadata {
    $1_fungible_asset_Metadata(s->$name, s->$symbol, s->$decimals, s->$icon_uri, x)
}
function $IsValid'$1_fungible_asset_Metadata'(s: $1_fungible_asset_Metadata): bool {
    $IsValid'$1_string_String'(s->$name)
      && $IsValid'$1_string_String'(s->$symbol)
      && $IsValid'u8'(s->$decimals)
      && $IsValid'$1_string_String'(s->$icon_uri)
      && $IsValid'$1_string_String'(s->$project_uri)
}
function {:inline} $IsEqual'$1_fungible_asset_Metadata'(s1: $1_fungible_asset_Metadata, s2: $1_fungible_asset_Metadata): bool {
    $IsEqual'$1_string_String'(s1->$name, s2->$name)
    && $IsEqual'$1_string_String'(s1->$symbol, s2->$symbol)
    && $IsEqual'u8'(s1->$decimals, s2->$decimals)
    && $IsEqual'$1_string_String'(s1->$icon_uri, s2->$icon_uri)
    && $IsEqual'$1_string_String'(s1->$project_uri, s2->$project_uri)}
var $1_fungible_asset_Metadata_$memory: $Memory $1_fungible_asset_Metadata;

// struct fungible_asset::MintRef at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/fungible_asset.move:184:5+73
datatype $1_fungible_asset_MintRef {
    $1_fungible_asset_MintRef($metadata: $1_object_Object'$1_fungible_asset_Metadata')
}
function {:inline} $Update'$1_fungible_asset_MintRef'_metadata(s: $1_fungible_asset_MintRef, x: $1_object_Object'$1_fungible_asset_Metadata'): $1_fungible_asset_MintRef {
    $1_fungible_asset_MintRef(x)
}
function $IsValid'$1_fungible_asset_MintRef'(s: $1_fungible_asset_MintRef): bool {
    $IsValid'$1_object_Object'$1_fungible_asset_Metadata''(s->$metadata)
}
function {:inline} $IsEqual'$1_fungible_asset_MintRef'(s1: $1_fungible_asset_MintRef, s2: $1_fungible_asset_MintRef): bool {
    s1 == s2
}

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:7:9+50
function  $1_aptos_hash_spec_keccak256(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_keccak256(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:12:9+58
function  $1_aptos_hash_spec_sha2_512_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_sha2_512_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:17:9+58
function  $1_aptos_hash_spec_sha3_512_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_sha3_512_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:22:9+59
function  $1_aptos_hash_spec_ripemd160_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_ripemd160_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:27:9+61
function  $1_aptos_hash_spec_blake2b_256_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_blake2b_256_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/big_vector.spec.move:131:10+102
function {:inline} $1_big_vector_spec_table_len'u64_vec'address''(t: Table int (Vec (int))): int {
    $1_table_with_length_spec_len'u64_vec'address''(t)
}

// spec fun at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/big_vector.spec.move:135:10+122
function {:inline} $1_big_vector_spec_table_contains'u64_vec'address''(t: Table int (Vec (int)), k: int): bool {
    $1_table_with_length_spec_contains'u64_vec'address''(t, k)
}

// struct big_vector::BigVector<address> at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/big_vector.move:18:5+136
datatype $1_big_vector_BigVector'address' {
    $1_big_vector_BigVector'address'($buckets: Table int (Vec (int)), $end_index: int, $bucket_size: int)
}
function {:inline} $Update'$1_big_vector_BigVector'address''_buckets(s: $1_big_vector_BigVector'address', x: Table int (Vec (int))): $1_big_vector_BigVector'address' {
    $1_big_vector_BigVector'address'(x, s->$end_index, s->$bucket_size)
}
function {:inline} $Update'$1_big_vector_BigVector'address''_end_index(s: $1_big_vector_BigVector'address', x: int): $1_big_vector_BigVector'address' {
    $1_big_vector_BigVector'address'(s->$buckets, x, s->$bucket_size)
}
function {:inline} $Update'$1_big_vector_BigVector'address''_bucket_size(s: $1_big_vector_BigVector'address', x: int): $1_big_vector_BigVector'address' {
    $1_big_vector_BigVector'address'(s->$buckets, s->$end_index, x)
}
function $IsValid'$1_big_vector_BigVector'address''(s: $1_big_vector_BigVector'address'): bool {
    $IsValid'$1_table_with_length_TableWithLength'u64_vec'address'''(s->$buckets)
      && $IsValid'u64'(s->$end_index)
      && $IsValid'u64'(s->$bucket_size)
}
function {:inline} $IsEqual'$1_big_vector_BigVector'address''(s1: $1_big_vector_BigVector'address', s2: $1_big_vector_BigVector'address'): bool {
    s1 == s2
}

// struct smart_vector::SmartVector<address> at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.move:23:5+181
datatype $1_smart_vector_SmartVector'address' {
    $1_smart_vector_SmartVector'address'($inline_vec: Vec (int), $big_vec: $1_option_Option'$1_big_vector_BigVector'address'', $inline_capacity: $1_option_Option'u64', $bucket_size: $1_option_Option'u64')
}
function {:inline} $Update'$1_smart_vector_SmartVector'address''_inline_vec(s: $1_smart_vector_SmartVector'address', x: Vec (int)): $1_smart_vector_SmartVector'address' {
    $1_smart_vector_SmartVector'address'(x, s->$big_vec, s->$inline_capacity, s->$bucket_size)
}
function {:inline} $Update'$1_smart_vector_SmartVector'address''_big_vec(s: $1_smart_vector_SmartVector'address', x: $1_option_Option'$1_big_vector_BigVector'address''): $1_smart_vector_SmartVector'address' {
    $1_smart_vector_SmartVector'address'(s->$inline_vec, x, s->$inline_capacity, s->$bucket_size)
}
function {:inline} $Update'$1_smart_vector_SmartVector'address''_inline_capacity(s: $1_smart_vector_SmartVector'address', x: $1_option_Option'u64'): $1_smart_vector_SmartVector'address' {
    $1_smart_vector_SmartVector'address'(s->$inline_vec, s->$big_vec, x, s->$bucket_size)
}
function {:inline} $Update'$1_smart_vector_SmartVector'address''_bucket_size(s: $1_smart_vector_SmartVector'address', x: $1_option_Option'u64'): $1_smart_vector_SmartVector'address' {
    $1_smart_vector_SmartVector'address'(s->$inline_vec, s->$big_vec, s->$inline_capacity, x)
}
function $IsValid'$1_smart_vector_SmartVector'address''(s: $1_smart_vector_SmartVector'address'): bool {
    $IsValid'vec'address''(s->$inline_vec)
      && $IsValid'$1_option_Option'$1_big_vector_BigVector'address'''(s->$big_vec)
      && $IsValid'$1_option_Option'u64''(s->$inline_capacity)
      && $IsValid'$1_option_Option'u64''(s->$bucket_size)
}
function {:inline} $IsEqual'$1_smart_vector_SmartVector'address''(s1: $1_smart_vector_SmartVector'address', s2: $1_smart_vector_SmartVector'address'): bool {
    $IsEqual'vec'address''(s1->$inline_vec, s2->$inline_vec)
    && $IsEqual'$1_option_Option'$1_big_vector_BigVector'address'''(s1->$big_vec, s2->$big_vec)
    && $IsEqual'$1_option_Option'u64''(s1->$inline_capacity, s2->$inline_capacity)
    && $IsEqual'$1_option_Option'u64''(s1->$bucket_size, s2->$bucket_size)}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:167:5+53
function {:inline} $aa_i32_$as_u32(v: $aa_i32_I32): bv32 {
    v->$bits
}

// struct i32::I32 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:11:5+58
datatype $aa_i32_I32 {
    $aa_i32_I32($bits: bv32)
}
function {:inline} $Update'$aa_i32_I32'_bits(s: $aa_i32_I32, x: bv32): $aa_i32_I32 {
    $aa_i32_I32(x)
}
function $IsValid'$aa_i32_I32'(s: $aa_i32_I32): bool {
    $IsValid'bv32'(s->$bits)
}
function {:inline} $IsEqual'$aa_i32_I32'(s1: $aa_i32_I32, s2: $aa_i32_I32): bool {
    s1 == s2
}

// fun i32::from [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:32:5+125
procedure {:inline 1} $aa_i32_from(_$t0: int) returns ($ret0: $aa_i32_I32)
{
    // declare local variables
    var $t1: int;
    var $t2: bool;
    var $t3: $aa_i32_I32;
    var $t4: int;
    var $t0: int;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'u32': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:32:5+1
    assume {:print "$at(7,523,524)"} true;
    assume {:print "$track_local(98,0,0):", $t0} $t0 == $t0;

    // $t1 := 2147483647 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:33:22+10
    assume {:print "$at(7,575,585)"} true;
    $t1 := 2147483647;
    assume $IsValid'u32'($t1);

    // $t2 := <=($t0, $t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:33:17+15
    call $t2 := $Le($t0, $t1);

    // if ($t2) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:33:9+6
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:34:9+35
    assume {:print "$at(7,607,642)"} true;
L1:

    // $t3 := pack 0xaa::i32::I32($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:34:9+35
    assume {:print "$at(7,607,642)"} true;
$t3 := $aa_i32_I32($int2bv.32($t0));

    // trace_return[0]($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:32:34+96
    assume {:print "$at(7,552,648)"} true;
    assume {:print "$track_return(98,0,0):", $t3} $t3 == $t3;

    // goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:32:34+96
    goto L2;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:33:34+9
    assume {:print "$at(7,587,596)"} true;
L0:

    // $t4 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:33:34+9
    assume {:print "$at(7,587,596)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:33:9+6
    assume {:print "$at(7,562,568)"} true;
    assume {:print "$track_abort(98,0):", $t4} $t4 == $t4;

    // goto L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:33:9+6
    goto L3;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:37:5+1
    assume {:print "$at(7,647,648)"} true;
L2:

    // return $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:37:5+1
    assume {:print "$at(7,647,648)"} true;
    $ret0 := $t3;
    return;

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:37:5+1
L3:

    // abort($t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:37:5+1
    assume {:print "$at(7,647,648)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun i32::cmp [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:179:5+299
procedure {:inline 1} $aa_i32_cmp(_$t0: $aa_i32_I32, _$t1: $aa_i32_I32) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: bool;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: bool;
    var $t19: int;
    var $t20: int;
    var $t0: $aa_i32_I32;
    var $t1: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'u8': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:179:5+1
    assume {:print "$at(7,3947,3948)"} true;
    assume {:print "$track_local(98,2,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:179:5+1
    assume {:print "$track_local(98,2,1):", $t1} $t1 == $t1;

    // $t2 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:180:13+9
    assume {:print "$at(7,4002,4011)"} true;
$t2 := $bv2int.32($t0->$bits);

    // $t3 := get_field<0xaa::i32::I32>.bits($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:180:26+9
$t3 := $bv2int.32($t1->$bits);

    // $t4 := ==($t2, $t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:180:13+22
    $t4 := $IsEqual'u32'($t2, $t3);

    // if ($t4) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:180:9+37
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:180:44+2
L1:

    // $t5 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:180:44+2
    assume {:print "$at(7,4033,4035)"} true;
    $t5 := 1;
    assume $IsValid'u8'($t5);

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:180:37+9
    assume {:print "$track_return(98,2,0):", $t5} $t5 == $t5;

    // $t6 := move($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:180:37+9
    $t6 := $t5;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:180:37+9
    goto L8;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:13+10
    assume {:print "$at(7,4049,4059)"} true;
L0:

    // $t7 := i32::sign($t0) on_abort goto L9 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:13+10
    assume {:print "$at(7,4049,4059)"} true;
    call $t7 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,4049,4059)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t9 := i32::sign($t1) on_abort goto L9 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:26+10
    call $t9 := $aa_i32_sign($t1);
    if ($abort_flag) {
        assume {:print "$at(7,4062,4072)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t10 := >($t7, $t9) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:13+23
    call $t10 := $Gt($t7, $t9);

    // if ($t10) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:9+38
    if ($t10) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:45+2
L3:

    // $t11 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:45+2
    assume {:print "$at(7,4081,4083)"} true;
    $t11 := 0;
    assume $IsValid'u8'($t11);

    // trace_return[0]($t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:38+9
    assume {:print "$track_return(98,2,0):", $t11} $t11 == $t11;

    // $t6 := move($t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:38+9
    $t6 := $t11;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:181:38+9
    goto L8;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:13+10
    assume {:print "$at(7,4097,4107)"} true;
L2:

    // $t12 := i32::sign($t0) on_abort goto L9 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:13+10
    assume {:print "$at(7,4097,4107)"} true;
    call $t12 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,4097,4107)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t13 := i32::sign($t1) on_abort goto L9 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:26+10
    call $t13 := $aa_i32_sign($t1);
    if ($abort_flag) {
        assume {:print "$at(7,4110,4120)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t14 := <($t12, $t13) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:13+23
    call $t14 := $Lt($t12, $t13);

    // if ($t14) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:9+38
    if ($t14) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:45+2
L5:

    // $t15 := 2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:45+2
    assume {:print "$at(7,4129,4131)"} true;
    $t15 := 2;
    assume $IsValid'u8'($t15);

    // trace_return[0]($t15) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:38+9
    assume {:print "$track_return(98,2,0):", $t15} $t15 == $t15;

    // $t6 := move($t15) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:38+9
    $t6 := $t15;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:182:38+9
    goto L8;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:183:13+4
    assume {:print "$at(7,4145,4149)"} true;
L4:

    // $t16 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:183:13+9
    assume {:print "$at(7,4145,4154)"} true;
$t16 := $bv2int.32($t0->$bits);

    // $t17 := get_field<0xaa::i32::I32>.bits($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:183:25+9
$t17 := $bv2int.32($t1->$bits);

    // $t18 := >($t16, $t17) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:183:13+21
    call $t18 := $Gt($t16, $t17);

    // if ($t18) goto L7 else goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:183:9+99
    if ($t18) { goto L7; } else { goto L6; }

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:184:20+2
    assume {:print "$at(7,4189,4191)"} true;
L7:

    // $t19 := 2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:184:20+2
    assume {:print "$at(7,4189,4191)"} true;
    $t19 := 2;
    assume $IsValid'u8'($t19);

    // trace_return[0]($t19) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:184:13+9
    assume {:print "$track_return(98,2,0):", $t19} $t19 == $t19;

    // $t6 := move($t19) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:184:13+9
    $t6 := $t19;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:184:13+9
    goto L8;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:186:20+2
    assume {:print "$at(7,4228,4230)"} true;
L6:

    // $t20 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:186:20+2
    assume {:print "$at(7,4228,4230)"} true;
    $t20 := 0;
    assume $IsValid'u8'($t20);

    // trace_return[0]($t20) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:186:13+9
    assume {:print "$track_return(98,2,0):", $t20} $t20 == $t20;

    // $t6 := move($t20) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:186:13+9
    $t6 := $t20;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:188:5+1
    assume {:print "$at(7,4245,4246)"} true;
L8:

    // return $t6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:188:5+1
    assume {:print "$at(7,4245,4246)"} true;
    $ret0 := $t6;
    return;

    // label L9 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:188:5+1
L9:

    // abort($t8) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:188:5+1
    assume {:print "$at(7,4245,4246)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun i32::sign [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:171:5+66
procedure {:inline 1} $aa_i32_sign(_$t0: $aa_i32_I32) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'u8': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:171:5+1
    assume {:print "$at(7,3809,3810)"} true;
    assume {:print "$track_local(98,8,0):", $t0} $t0 == $t0;

    // $t1 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:172:11+6
    assume {:print "$at(7,3849,3855)"} true;
$t1 := $bv2int.32($t0->$bits);

    // $t2 := 31 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:172:21+2
    $t2 := 31;
    assume $IsValid'u8'($t2);

    // $t3 := >>($t1, $t2) on_abort goto L2 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:172:10+14
    call $t3 := $ShrU32($t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(7,3848,3862)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(98,8):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := (u8)($t3) on_abort goto L2 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:172:9+22
    call $t5 := $CastU8($t3);
    if ($abort_flag) {
        assume {:print "$at(7,3847,3869)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(98,8):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:172:9+22
    assume {:print "$track_return(98,8,0):", $t5} $t5 == $t5;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:173:5+1
    assume {:print "$at(7,3874,3875)"} true;
L1:

    // return $t5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:173:5+1
    assume {:print "$at(7,3874,3875)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:173:5+1
L2:

    // abort($t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:173:5+1
    assume {:print "$at(7,3874,3875)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun i32::abs [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:119:5+231
procedure {:inline 1} $aa_i32_abs(_$t0: $aa_i32_I32) returns ($ret0: $aa_i32_I32)
{
    // declare local variables
    var $t1: $aa_i32_I32;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: bool;
    var $t6: bv32;
    var $t7: bv32;
    var $t8: bool;
    var $t9: bv32;
    var $t10: bv32;
    var $t11: bv32;
    var $t12: bv32;
    var $t13: $aa_i32_I32;
    var $t14: int;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:119:5+1
    assume {:print "$at(7,2717,2718)"} true;
    assume {:print "$track_local(98,9,0):", $t0} $t0 == $t0;

    // $t2 := i32::sign($t0) on_abort goto L6 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:120:13+7
    assume {:print "$at(7,2759,2766)"} true;
    call $t2 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,2759,2766)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,9):", $t3} $t3 == $t3;
        goto L6;
    }

    // $t4 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:120:24+1
    $t4 := 0;
    assume $IsValid'u8'($t4);

    // $t5 := ==($t2, $t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:120:13+12
    $t5 := $IsEqual'u8'($t2, $t4);

    // if ($t5) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:120:9+187
    if ($t5) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:121:13+1
    assume {:print "$at(7,2787,2788)"} true;
L1:

    // $t1 := $t0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:121:13+1
    assume {:print "$at(7,2787,2788)"} true;
    $t1 := $t0;

    // trace_local[return]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:121:13+1
    assume {:print "$track_local(98,9,1):", $t0} $t0 == $t0;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:120:9+187
    assume {:print "$at(7,2755,2942)"} true;
L4:

    // trace_return[0]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:120:9+187
    assume {:print "$at(7,2755,2942)"} true;
    assume {:print "$track_return(98,9,0):", $t1} $t1 == $t1;

    // goto L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:120:9+187
    goto L5;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:21+1
    assume {:print "$at(7,2826,2827)"} true;
L0:

    // $t6 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:21+6
    assume {:print "$at(7,2826,2832)"} true;
    $t6 := $t0->$bits;

    // $t7 := 2147483648 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:30+10
    $t7 := 2147483648bv32;
    assume $IsValid'bv32'($t7);

    // $t8 := >($t6, $t7) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:21+19
    call $t8 := $GtBv32($t6, $t7);

    // if ($t8) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:13+6
    if ($t8) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:125:31+1
    assume {:print "$at(7,2907,2908)"} true;
L3:

    // $t9 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:125:31+6
    assume {:print "$at(7,2907,2913)"} true;
    $t9 := $t0->$bits;

    // $t10 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:125:40+1
    $t10 := 1bv32;
    assume $IsValid'bv32'($t10);

    // $t11 := -($t9, $t10) on_abort goto L6 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:125:31+10
    call $t11 := $SubBv32($t9, $t10);
    if ($abort_flag) {
        assume {:print "$at(7,2907,2917)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,9):", $t3} $t3 == $t3;
        goto L6;
    }

    // $t12 := i32::u32_neg($t11) on_abort goto L6 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:125:23+19
    call $t12 := $aa_i32_u32_neg($t11);
    if ($abort_flag) {
        assume {:print "$at(7,2899,2918)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,9):", $t3} $t3 == $t3;
        goto L6;
    }

    // $t13 := pack 0xaa::i32::I32($t12) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:124:13+61
    assume {:print "$at(7,2871,2932)"} true;
    $t13 := $aa_i32_I32($t12);

    // $t1 := $t13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:124:13+61
    $t1 := $t13;

    // trace_local[return]($t13) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:124:13+61
    assume {:print "$track_local(98,9,1):", $t13} $t13 == $t13;

    // goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:124:13+61
    goto L4;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:42+9
    assume {:print "$at(7,2847,2856)"} true;
L2:

    // $t14 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:42+9
    assume {:print "$at(7,2847,2856)"} true;
    $t14 := 0;
    assume $IsValid'u64'($t14);

    // trace_abort($t14) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:13+6
    assume {:print "$at(7,2818,2824)"} true;
    assume {:print "$track_abort(98,9):", $t14} $t14 == $t14;

    // $t3 := move($t14) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:13+6
    $t3 := $t14;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:123:13+6
    goto L6;

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:128:5+1
    assume {:print "$at(7,2947,2948)"} true;
L5:

    // return $t1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:128:5+1
    assume {:print "$at(7,2947,2948)"} true;
    $ret0 := $t1;
    return;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:128:5+1
L6:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:128:5+1
    assume {:print "$at(7,2947,2948)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun i32::as_u32 [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:167:5+53
procedure {:inline 1} $aa_i32_as_u32(_$t0: $aa_i32_I32) returns ($ret0: bv32)
{
    // declare local variables
    var $t1: bv32;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'bv32': bv32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:167:5+1
    assume {:print "$at(7,3750,3751)"} true;
    assume {:print "$track_local(98,12,0):", $t0} $t0 == $t0;

    // $t1 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:168:9+6
    assume {:print "$at(7,3791,3797)"} true;
    $t1 := $t0->$bits;

    // trace_return[0]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:168:9+6
    assume {:print "$track_return(98,12,0):", $t1} $t1 == $t1;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:169:5+1
    assume {:print "$at(7,3802,3803)"} true;
L1:

    // return $t1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:169:5+1
    assume {:print "$at(7,3802,3803)"} true;
    $ret0 := $t1;
    return;

}

// fun i32::gte [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:198:5+80
procedure {:inline 1} $aa_i32_gte(_$t0: $aa_i32_I32, _$t1: $aa_i32_I32) returns ($ret0: bool)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: bool;
    var $t0: $aa_i32_I32;
    var $t1: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'bool': bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:198:5+1
    assume {:print "$at(7,4423,4424)"} true;
    assume {:print "$track_local(98,15,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:198:5+1
    assume {:print "$track_local(98,15,1):", $t1} $t1 == $t1;

    // $t2 := i32::cmp($t0, $t1) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:199:9+15
    assume {:print "$at(7,4476,4491)"} true;
    call $t2 := $aa_i32_cmp($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(7,4476,4491)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,15):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:199:28+2
    $t4 := 1;
    assume $IsValid'u8'($t4);

    // $t5 := >=($t2, $t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:199:9+21
    call $t5 := $Ge($t2, $t4);

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:199:9+21
    assume {:print "$track_return(98,15,0):", $t5} $t5 == $t5;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:200:5+1
    assume {:print "$at(7,4502,4503)"} true;
L1:

    // return $t5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:200:5+1
    assume {:print "$at(7,4502,4503)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:200:5+1
L2:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:200:5+1
    assume {:print "$at(7,4502,4503)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun i32::is_neg [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:175:5+60
procedure {:inline 1} $aa_i32_is_neg(_$t0: $aa_i32_I32) returns ($ret0: bool)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'bool': bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:175:5+1
    assume {:print "$at(7,3881,3882)"} true;
    assume {:print "$track_local(98,17,0):", $t0} $t0 == $t0;

    // $t1 := i32::sign($t0) on_abort goto L2 with $t2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:176:9+7
    assume {:print "$at(7,3923,3930)"} true;
    call $t1 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,3923,3930)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(98,17):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:176:20+1
    $t3 := 1;
    assume $IsValid'u8'($t3);

    // $t4 := ==($t1, $t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:176:9+12
    $t4 := $IsEqual'u8'($t1, $t3);

    // trace_return[0]($t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:176:9+12
    assume {:print "$track_return(98,17,0):", $t4} $t4 == $t4;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:177:5+1
    assume {:print "$at(7,3940,3941)"} true;
L1:

    // return $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:177:5+1
    assume {:print "$at(7,3940,3941)"} true;
    $ret0 := $t4;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:177:5+1
L2:

    // abort($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:177:5+1
    assume {:print "$at(7,3940,3941)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun i32::lt [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:202:5+79
procedure {:inline 1} $aa_i32_lt(_$t0: $aa_i32_I32, _$t1: $aa_i32_I32) returns ($ret0: bool)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: bool;
    var $t0: $aa_i32_I32;
    var $t1: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'bool': bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:202:5+1
    assume {:print "$at(7,4509,4510)"} true;
    assume {:print "$track_local(98,18,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:202:5+1
    assume {:print "$track_local(98,18,1):", $t1} $t1 == $t1;

    // $t2 := i32::cmp($t0, $t1) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:203:9+15
    assume {:print "$at(7,4561,4576)"} true;
    call $t2 := $aa_i32_cmp($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(7,4561,4576)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,18):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:203:28+2
    $t4 := 0;
    assume $IsValid'u8'($t4);

    // $t5 := ==($t2, $t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:203:9+21
    $t5 := $IsEqual'u8'($t2, $t4);

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:203:9+21
    assume {:print "$track_return(98,18,0):", $t5} $t5 == $t5;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:204:5+1
    assume {:print "$at(7,4587,4588)"} true;
L1:

    // return $t5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:204:5+1
    assume {:print "$at(7,4587,4588)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:204:5+1
L2:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:204:5+1
    assume {:print "$at(7,4587,4588)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun i32::lte [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:206:5+80
procedure {:inline 1} $aa_i32_lte(_$t0: $aa_i32_I32, _$t1: $aa_i32_I32) returns ($ret0: bool)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: bool;
    var $t0: $aa_i32_I32;
    var $t1: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'bool': bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:206:5+1
    assume {:print "$at(7,4594,4595)"} true;
    assume {:print "$track_local(98,19,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:206:5+1
    assume {:print "$track_local(98,19,1):", $t1} $t1 == $t1;

    // $t2 := i32::cmp($t0, $t1) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:207:9+15
    assume {:print "$at(7,4647,4662)"} true;
    call $t2 := $aa_i32_cmp($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(7,4647,4662)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,19):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:207:28+2
    $t4 := 1;
    assume $IsValid'u8'($t4);

    // $t5 := <=($t2, $t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:207:9+21
    call $t5 := $Le($t2, $t4);

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:207:9+21
    assume {:print "$track_return(98,19,0):", $t5} $t5 == $t5;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:208:5+1
    assume {:print "$at(7,4673,4674)"} true;
L1:

    // return $t5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:208:5+1
    assume {:print "$at(7,4673,4674)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:208:5+1
L2:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:208:5+1
    assume {:print "$at(7,4673,4674)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun i32::neg_from [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:54:5+273
procedure {:inline 1} $aa_i32_neg_from(_$t0: bv32) returns ($ret0: $aa_i32_I32)
{
    // declare local variables
    var $t1: $aa_i32_I32;
    var $t2: bv32;
    var $t3: bool;
    var $t4: bv32;
    var $t5: bool;
    var $t6: $aa_i32_I32;
    var $t7: bv32;
    var $t8: int;
    var $t9: bv32;
    var $t10: bv32;
    var $t11: int;
    var $t12: bv32;
    var $t13: $aa_i32_I32;
    var $t14: int;
    var $t0: bv32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'bv32': bv32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:54:5+1
    assume {:print "$at(7,967,968)"} true;
    assume {:print "$track_local(98,21,0):", $t0} $t0 == $t0;

    // $t2 := 2147483648 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:55:22+10
    assume {:print "$at(7,1023,1033)"} true;
    $t2 := 2147483648bv32;
    assume $IsValid'bv32'($t2);

    // $t3 := <=($t0, $t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:55:17+15
    call $t3 := $LeBv32($t0, $t2);

    // if ($t3) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:55:9+6
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:56:13+1
    assume {:print "$at(7,1059,1060)"} true;
L1:

    // $t4 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:56:18+1
    assume {:print "$at(7,1064,1065)"} true;
    $t4 := 0bv32;
    assume $IsValid'bv32'($t4);

    // $t5 := ==($t0, $t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:56:13+6
    $t5 := $IsEqual'bv32'($t0, $t4);

    // if ($t5) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:56:9+179
    if ($t5) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:57:13+43
    assume {:print "$at(7,1081,1124)"} true;
L3:

    // $t6 := pack 0xaa::i32::I32($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:57:13+43
    assume {:print "$at(7,1081,1124)"} true;
    $t6 := $aa_i32_I32($t0);

    // $t1 := $t6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:57:13+43
    $t1 := $t6;

    // trace_local[return]($t6) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:57:13+43
    assume {:print "$track_local(98,21,1):", $t6} $t6 == $t6;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:54:38+240
    assume {:print "$at(7,1000,1240)"} true;
L4:

    // trace_return[0]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:54:38+240
    assume {:print "$at(7,1000,1240)"} true;
    assume {:print "$track_return(98,21,0):", $t1} $t1 == $t1;

    // goto L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:54:38+240
    goto L5;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:62:24+10
    assume {:print "$at(7,1183,1193)"} true;
L2:

    // $t7 := i32::u32_neg($t0) on_abort goto L6 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:62:24+10
    assume {:print "$at(7,1183,1193)"} true;
    call $t7 := $aa_i32_u32_neg($t0);
    if ($abort_flag) {
        assume {:print "$at(7,1183,1193)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,21):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t9 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:62:37+1
    $t9 := 1bv32;
    assume $IsValid'bv32'($t9);

    // $t10 := +($t7, $t9) on_abort goto L6 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:62:23+16
    call $t10 := $AddBv32($t7, $t9);
    if ($abort_flag) {
        assume {:print "$at(7,1182,1198)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,21):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t11 := 2147483648 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:62:42+9
    $t11 := 2147483648;
    assume $IsValid'u32'($t11);

    // $t12 := |($t10, $t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:62:23+28
    call $t12 := $OrBv32($t10, $int2bv.32($t11));

    // $t13 := pack 0xaa::i32::I32($t12) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:61:13+70
    assume {:print "$at(7,1154,1224)"} true;
    $t13 := $aa_i32_I32($t12);

    // $t1 := $t13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:61:13+70
    $t1 := $t13;

    // trace_local[return]($t13) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:61:13+70
    assume {:print "$track_local(98,21,1):", $t13} $t13 == $t13;

    // goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:61:13+70
    goto L4;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:55:34+9
    assume {:print "$at(7,1035,1044)"} true;
L0:

    // $t14 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:55:34+9
    assume {:print "$at(7,1035,1044)"} true;
    $t14 := 0;
    assume $IsValid'u64'($t14);

    // trace_abort($t14) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:55:9+6
    assume {:print "$at(7,1010,1016)"} true;
    assume {:print "$track_abort(98,21):", $t14} $t14 == $t14;

    // $t8 := move($t14) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:55:9+6
    $t8 := $t14;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:55:9+6
    goto L6;

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:65:5+1
    assume {:print "$at(7,1239,1240)"} true;
L5:

    // return $t1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:65:5+1
    assume {:print "$at(7,1239,1240)"} true;
    $ret0 := $t1;
    return;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:65:5+1
L6:

    // abort($t8) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:65:5+1
    assume {:print "$at(7,1239,1240)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun i32::u32_neg [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:244:5+55
procedure {:inline 1} $aa_i32_u32_neg(_$t0: bv32) returns ($ret0: bv32)
{
    // declare local variables
    var $t1: int;
    var $t2: bv32;
    var $t0: bv32;
    var $temp_0'bv32': bv32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:244:5+1
    assume {:print "$at(7,5531,5532)"} true;
    assume {:print "$track_local(98,26,0):", $t0} $t0 == $t0;

    // $t1 := 4294967295 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:245:13+10
    assume {:print "$at(7,5570,5580)"} true;
    $t1 := 4294967295;
    assume $IsValid'u32'($t1);

    // $t2 := ^($t0, $t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:245:9+14
    call $t2 := $XorBv32($t0, $int2bv.32($t1));

    // trace_return[0]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:245:9+14
    assume {:print "$track_return(98,26,0):", $t2} $t2 == $t2;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:246:5+1
    assume {:print "$at(7,5585,5586)"} true;
L1:

    // return $t2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i32.move:246:5+1
    assume {:print "$at(7,5585,5586)"} true;
    $ret0 := $t2;
    return;

}

// struct i128::I128 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/i128.move:15:5+60
datatype $aa_i128_I128 {
    $aa_i128_I128($bits: int)
}
function {:inline} $Update'$aa_i128_I128'_bits(s: $aa_i128_I128, x: int): $aa_i128_I128 {
    $aa_i128_I128(x)
}
function $IsValid'$aa_i128_I128'(s: $aa_i128_I128): bool {
    $IsValid'u128'(s->$bits)
}
function {:inline} $IsEqual'$aa_i128_I128'(s1: $aa_i128_I128, s2: $aa_i128_I128): bool {
    s1 == s2
}

// fun full_math_u128::full_mul [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:28:5+97
procedure {:inline 1} $aa_full_math_u128_full_mul(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u128': int;
    var $temp_0'u256': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:28:5+1
    assume {:print "$at(4,885,886)"} true;
    assume {:print "$track_local(101,0,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:28:5+1
    assume {:print "$track_local(101,0,1):", $t1} $t1 == $t1;

    // $t2 := (u256)($t0) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:29:9+14
    assume {:print "$at(4,945,959)"} true;
    call $t2 := $CastU256($t0);
    if ($abort_flag) {
        assume {:print "$at(4,945,959)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(101,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := (u256)($t1) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:29:26+14
    call $t4 := $CastU256($t1);
    if ($abort_flag) {
        assume {:print "$at(4,962,976)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(101,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t5 := *($t2, $t4) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:29:9+31
    call $t5 := $MulU256($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(4,945,976)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(101,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:29:9+31
    assume {:print "$track_return(101,0,0):", $t5} $t5 == $t5;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:30:5+1
    assume {:print "$at(4,981,982)"} true;
L1:

    // return $t5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:30:5+1
    assume {:print "$at(4,981,982)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:30:5+1
L2:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:30:5+1
    assume {:print "$at(4,981,982)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun full_math_u128::full_mul_v2 [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:32:5+100
procedure {:inline 1} $aa_full_math_u128_full_mul_v2(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u128': int;
    var $temp_0'u256': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:32:5+1
    assume {:print "$at(4,988,989)"} true;
    assume {:print "$track_local(101,1,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:32:5+1
    assume {:print "$track_local(101,1,1):", $t1} $t1 == $t1;

    // $t2 := (u256)($t0) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:33:9+14
    assume {:print "$at(4,1051,1065)"} true;
    call $t2 := $CastU256($t0);
    if ($abort_flag) {
        assume {:print "$at(4,1051,1065)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(101,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := (u256)($t1) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:33:26+14
    call $t4 := $CastU256($t1);
    if ($abort_flag) {
        assume {:print "$at(4,1068,1082)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(101,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t5 := *($t2, $t4) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:33:9+31
    call $t5 := $MulU256($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(4,1051,1082)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(101,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:33:9+31
    assume {:print "$track_return(101,1,0):", $t5} $t5 == $t5;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:34:5+1
    assume {:print "$at(4,1087,1088)"} true;
L1:

    // return $t5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:34:5+1
    assume {:print "$at(4,1087,1088)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:34:5+1
L2:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:34:5+1
    assume {:print "$at(4,1087,1088)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun full_math_u128::mul_shr [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:18:5+149
procedure {:inline 1} $aa_full_math_u128_mul_shr(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: int)
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'u128': int;
    var $temp_0'u8': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:18:5+1
    assume {:print "$at(4,575,576)"} true;
    assume {:print "$track_local(101,6,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:18:5+1
    assume {:print "$track_local(101,6,1):", $t1} $t1 == $t1;

    // trace_local[shift]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:18:5+1
    assume {:print "$track_local(101,6,2):", $t2} $t2 == $t2;

    // $t3 := full_math_u128::full_mul_v2($t0, $t1) on_abort goto L2 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:19:23+23
    assume {:print "$at(4,659,682)"} true;
    call $t3 := $aa_full_math_u128_full_mul_v2($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(4,659,682)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(101,6):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := >>($t3, $t2) on_abort goto L2 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:19:23+32
    call $t5 := $ShrU256($t3, $t2);
    if ($abort_flag) {
        assume {:print "$at(4,659,691)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(101,6):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t6 := (u128)($t5) on_abort goto L2 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:20:9+17
    assume {:print "$at(4,701,718)"} true;
    call $t6 := $CastU128($t5);
    if ($abort_flag) {
        assume {:print "$at(4,701,718)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(101,6):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t6) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:20:9+17
    assume {:print "$track_return(101,6,0):", $t6} $t6 == $t6;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:21:5+1
    assume {:print "$at(4,723,724)"} true;
L1:

    // return $t6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:21:5+1
    assume {:print "$at(4,723,724)"} true;
    $ret0 := $t6;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:21:5+1
L2:

    // abort($t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/full_math_u128.move:21:5+1
    assume {:print "$at(4,723,724)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun tick_math::get_sqrt_price_at_negative_tick [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:136:5+2643
procedure {:inline 1} $aa_tick_math_get_sqrt_price_at_negative_tick(_$t0: $aa_i32_I32) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: $aa_i32_I32;
    var $t4: int;
    var $t5: bv32;
    var $t6: int;
    var $t7: bv32;
    var $t8: bv32;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t12: bv32;
    var $t13: bv32;
    var $t14: bool;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: bv32;
    var $t20: bv32;
    var $t21: bool;
    var $t22: int;
    var $t23: int;
    var $t24: int;
    var $t25: int;
    var $t26: bv32;
    var $t27: bv32;
    var $t28: bool;
    var $t29: int;
    var $t30: int;
    var $t31: int;
    var $t32: int;
    var $t33: bv32;
    var $t34: bv32;
    var $t35: bool;
    var $t36: int;
    var $t37: int;
    var $t38: int;
    var $t39: int;
    var $t40: bv32;
    var $t41: bv32;
    var $t42: bool;
    var $t43: int;
    var $t44: int;
    var $t45: int;
    var $t46: int;
    var $t47: bv32;
    var $t48: bv32;
    var $t49: bool;
    var $t50: int;
    var $t51: int;
    var $t52: int;
    var $t53: int;
    var $t54: bv32;
    var $t55: bv32;
    var $t56: bool;
    var $t57: int;
    var $t58: int;
    var $t59: int;
    var $t60: int;
    var $t61: bv32;
    var $t62: bv32;
    var $t63: bool;
    var $t64: int;
    var $t65: int;
    var $t66: int;
    var $t67: int;
    var $t68: bv32;
    var $t69: bv32;
    var $t70: bool;
    var $t71: int;
    var $t72: int;
    var $t73: int;
    var $t74: int;
    var $t75: bv32;
    var $t76: bv32;
    var $t77: bool;
    var $t78: int;
    var $t79: int;
    var $t80: int;
    var $t81: int;
    var $t82: bv32;
    var $t83: bv32;
    var $t84: bool;
    var $t85: int;
    var $t86: int;
    var $t87: int;
    var $t88: int;
    var $t89: bv32;
    var $t90: bv32;
    var $t91: bool;
    var $t92: int;
    var $t93: int;
    var $t94: int;
    var $t95: int;
    var $t96: bv32;
    var $t97: bv32;
    var $t98: bool;
    var $t99: int;
    var $t100: int;
    var $t101: int;
    var $t102: int;
    var $t103: bv32;
    var $t104: bv32;
    var $t105: bool;
    var $t106: int;
    var $t107: int;
    var $t108: int;
    var $t109: int;
    var $t110: bv32;
    var $t111: bv32;
    var $t112: bool;
    var $t113: int;
    var $t114: int;
    var $t115: int;
    var $t116: int;
    var $t117: bv32;
    var $t118: bv32;
    var $t119: bool;
    var $t120: int;
    var $t121: int;
    var $t122: int;
    var $t123: int;
    var $t124: bv32;
    var $t125: bv32;
    var $t126: bool;
    var $t127: int;
    var $t128: int;
    var $t129: int;
    var $t130: int;
    var $t131: bv32;
    var $t132: bv32;
    var $t133: bool;
    var $t134: int;
    var $t135: int;
    var $t136: int;
    var $t137: int;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'u128': int;
    var $temp_0'bv32': bv32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[tick]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:136:5+1
    assume {:print "$at(13,4194,4195)"} true;
    assume {:print "$track_local(102,3,0):", $t0} $t0 == $t0;

    // $t3 := i32::abs($t0) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:137:36+14
    assume {:print "$at(13,4289,4303)"} true;
    call $t3 := $aa_i32_abs($t0);
    if ($abort_flag) {
        assume {:print "$at(13,4289,4303)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t5 := i32::as_u32($t3) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:137:24+27
    call $t5 := $aa_i32_as_u32($t3);
    if ($abort_flag) {
        assume {:print "$at(13,4277,4304)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // trace_local[abs_tick]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:137:24+27
    assume {:print "$track_local(102,3,1):", $t5} $t5 == $t5;

    // $t6 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:138:36+3
    assume {:print "$at(13,4341,4344)"} true;
    $t6 := 1;
    assume $IsValid'u32'($t6);

    // $t7 := &($t5, $t6) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:138:25+14
    call $t7 := $AndBv32($t5, $int2bv.32($t6));

    // $t8 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:138:43+1
    $t8 := 0bv32;
    assume $IsValid'bv32'($t8);

    // $t9 := !=($t7, $t8) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:138:25+19
    $t9 := !$IsEqual'bv32'($t7, $t8);

    // if ($t9) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:138:21+127
    if ($t9) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:139:13+24
    assume {:print "$at(13,4365,4389)"} true;
L1:

    // $t10 := 18445821805675392311 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:139:13+24
    assume {:print "$at(13,4365,4389)"} true;
    $t10 := 18445821805675392311;
    assume $IsValid'u128'($t10);

    // $t2 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:139:13+24
    $t2 := $t10;

    // trace_local[ratio]($t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:139:13+24
    assume {:print "$track_local(102,3,2):", $t10} $t10 == $t10;

    // label L56 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:143:13+8
    assume {:print "$at(13,4467,4475)"} true;
L56:

    // $t11 := 2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:143:24+3
    assume {:print "$at(13,4478,4481)"} true;
    $t11 := 2;
    assume $IsValid'u32'($t11);

    // $t12 := &($t5, $t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:143:13+14
    call $t12 := $AndBv32($t5, $int2bv.32($t11));

    // $t13 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:143:31+1
    $t13 := 0bv32;
    assume $IsValid'bv32'($t13);

    // $t14 := !=($t12, $t13) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:143:13+19
    $t14 := !$IsEqual'bv32'($t12, $t13);

    // if ($t14) goto L2 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:143:9+119
    if ($t14) { goto L2; } else { goto L4; }

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:144:45+5
    assume {:print "$at(13,4534,4539)"} true;
L2:

    // $t15 := 18444899583751176498 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:144:52+24
    assume {:print "$at(13,4541,4565)"} true;
    $t15 := 18444899583751176498;
    assume $IsValid'u128'($t15);

    // $t16 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:144:78+4
    $t16 := 64;
    assume $IsValid'u8'($t16);

    // $t17 := full_math_u128::mul_shr($t2, $t15, $t16) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:144:21+62
    call $t17 := $aa_full_math_u128_mul_shr($t2, $t15, $t16);
    if ($abort_flag) {
        assume {:print "$at(13,4510,4572)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:144:13+70
    $t2 := $t17;

    // trace_local[ratio]($t17) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:144:13+70
    assume {:print "$track_local(102,3,2):", $t17} $t17 == $t17;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:146:13+8
    assume {:print "$at(13,4596,4604)"} true;
L4:

    // $t18 := 4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:146:24+3
    assume {:print "$at(13,4607,4610)"} true;
    $t18 := 4;
    assume $IsValid'u32'($t18);

    // $t19 := &($t5, $t18) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:146:13+14
    call $t19 := $AndBv32($t5, $int2bv.32($t18));

    // $t20 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:146:31+1
    $t20 := 0bv32;
    assume $IsValid'bv32'($t20);

    // $t21 := !=($t19, $t20) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:146:13+19
    $t21 := !$IsEqual'bv32'($t19, $t20);

    // if ($t21) goto L5 else goto L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:146:9+120
    if ($t21) { goto L5; } else { goto L7; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:147:45+5
    assume {:print "$at(13,4663,4668)"} true;
L5:

    // $t22 := 18443055278223354162 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:147:52+24
    assume {:print "$at(13,4670,4694)"} true;
    $t22 := 18443055278223354162;
    assume $IsValid'u128'($t22);

    // $t23 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:147:78+4
    $t23 := 64;
    assume $IsValid'u8'($t23);

    // $t24 := full_math_u128::mul_shr($t2, $t22, $t23) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:147:21+62
    call $t24 := $aa_full_math_u128_mul_shr($t2, $t22, $t23);
    if ($abort_flag) {
        assume {:print "$at(13,4639,4701)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t24 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:147:13+70
    $t2 := $t24;

    // trace_local[ratio]($t24) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:147:13+70
    assume {:print "$track_local(102,3,2):", $t24} $t24 == $t24;

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:149:13+8
    assume {:print "$at(13,4726,4734)"} true;
L7:

    // $t25 := 8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:149:24+3
    assume {:print "$at(13,4737,4740)"} true;
    $t25 := 8;
    assume $IsValid'u32'($t25);

    // $t26 := &($t5, $t25) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:149:13+14
    call $t26 := $AndBv32($t5, $int2bv.32($t25));

    // $t27 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:149:31+1
    $t27 := 0bv32;
    assume $IsValid'bv32'($t27);

    // $t28 := !=($t26, $t27) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:149:13+19
    $t28 := !$IsEqual'bv32'($t26, $t27);

    // if ($t28) goto L8 else goto L10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:149:9+120
    if ($t28) { goto L8; } else { goto L10; }

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:150:45+5
    assume {:print "$at(13,4793,4798)"} true;
L8:

    // $t29 := 18439367220385604838 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:150:52+24
    assume {:print "$at(13,4800,4824)"} true;
    $t29 := 18439367220385604838;
    assume $IsValid'u128'($t29);

    // $t30 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:150:78+4
    $t30 := 64;
    assume $IsValid'u8'($t30);

    // $t31 := full_math_u128::mul_shr($t2, $t29, $t30) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:150:21+62
    call $t31 := $aa_full_math_u128_mul_shr($t2, $t29, $t30);
    if ($abort_flag) {
        assume {:print "$at(13,4769,4831)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t31 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:150:13+70
    $t2 := $t31;

    // trace_local[ratio]($t31) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:150:13+70
    assume {:print "$track_local(102,3,2):", $t31} $t31 == $t31;

    // label L10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:152:13+8
    assume {:print "$at(13,4856,4864)"} true;
L10:

    // $t32 := 16 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:152:24+4
    assume {:print "$at(13,4867,4871)"} true;
    $t32 := 16;
    assume $IsValid'u32'($t32);

    // $t33 := &($t5, $t32) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:152:13+15
    call $t33 := $AndBv32($t5, $int2bv.32($t32));

    // $t34 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:152:32+1
    $t34 := 0bv32;
    assume $IsValid'bv32'($t34);

    // $t35 := !=($t33, $t34) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:152:13+20
    $t35 := !$IsEqual'bv32'($t33, $t34);

    // if ($t35) goto L11 else goto L13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:152:9+121
    if ($t35) { goto L11; } else { goto L13; }

    // label L11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:153:45+5
    assume {:print "$at(13,4924,4929)"} true;
L11:

    // $t36 := 18431993317065449817 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:153:52+24
    assume {:print "$at(13,4931,4955)"} true;
    $t36 := 18431993317065449817;
    assume $IsValid'u128'($t36);

    // $t37 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:153:78+4
    $t37 := 64;
    assume $IsValid'u8'($t37);

    // $t38 := full_math_u128::mul_shr($t2, $t36, $t37) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:153:21+62
    call $t38 := $aa_full_math_u128_mul_shr($t2, $t36, $t37);
    if ($abort_flag) {
        assume {:print "$at(13,4900,4962)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t38 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:153:13+70
    $t2 := $t38;

    // trace_local[ratio]($t38) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:153:13+70
    assume {:print "$track_local(102,3,2):", $t38} $t38 == $t38;

    // label L13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:155:13+8
    assume {:print "$at(13,4987,4995)"} true;
L13:

    // $t39 := 32 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:155:24+4
    assume {:print "$at(13,4998,5002)"} true;
    $t39 := 32;
    assume $IsValid'u32'($t39);

    // $t40 := &($t5, $t39) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:155:13+15
    call $t40 := $AndBv32($t5, $int2bv.32($t39));

    // $t41 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:155:32+1
    $t41 := 0bv32;
    assume $IsValid'bv32'($t41);

    // $t42 := !=($t40, $t41) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:155:13+20
    $t42 := !$IsEqual'bv32'($t40, $t41);

    // if ($t42) goto L14 else goto L16 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:155:9+121
    if ($t42) { goto L14; } else { goto L16; }

    // label L14 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:156:45+5
    assume {:print "$at(13,5055,5060)"} true;
L14:

    // $t43 := 18417254355718160513 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:156:52+24
    assume {:print "$at(13,5062,5086)"} true;
    $t43 := 18417254355718160513;
    assume $IsValid'u128'($t43);

    // $t44 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:156:78+4
    $t44 := 64;
    assume $IsValid'u8'($t44);

    // $t45 := full_math_u128::mul_shr($t2, $t43, $t44) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:156:21+62
    call $t45 := $aa_full_math_u128_mul_shr($t2, $t43, $t44);
    if ($abort_flag) {
        assume {:print "$at(13,5031,5093)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t45 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:156:13+70
    $t2 := $t45;

    // trace_local[ratio]($t45) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:156:13+70
    assume {:print "$track_local(102,3,2):", $t45} $t45 == $t45;

    // label L16 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:158:13+8
    assume {:print "$at(13,5118,5126)"} true;
L16:

    // $t46 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:158:24+4
    assume {:print "$at(13,5129,5133)"} true;
    $t46 := 64;
    assume $IsValid'u32'($t46);

    // $t47 := &($t5, $t46) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:158:13+15
    call $t47 := $AndBv32($t5, $int2bv.32($t46));

    // $t48 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:158:32+1
    $t48 := 0bv32;
    assume $IsValid'bv32'($t48);

    // $t49 := !=($t47, $t48) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:158:13+20
    $t49 := !$IsEqual'bv32'($t47, $t48);

    // if ($t49) goto L17 else goto L19 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:158:9+121
    if ($t49) { goto L17; } else { goto L19; }

    // label L17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:159:45+5
    assume {:print "$at(13,5186,5191)"} true;
L17:

    // $t50 := 18387811781193591352 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:159:52+24
    assume {:print "$at(13,5193,5217)"} true;
    $t50 := 18387811781193591352;
    assume $IsValid'u128'($t50);

    // $t51 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:159:78+4
    $t51 := 64;
    assume $IsValid'u8'($t51);

    // $t52 := full_math_u128::mul_shr($t2, $t50, $t51) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:159:21+62
    call $t52 := $aa_full_math_u128_mul_shr($t2, $t50, $t51);
    if ($abort_flag) {
        assume {:print "$at(13,5162,5224)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t52 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:159:13+70
    $t2 := $t52;

    // trace_local[ratio]($t52) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:159:13+70
    assume {:print "$track_local(102,3,2):", $t52} $t52 == $t52;

    // label L19 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:161:13+8
    assume {:print "$at(13,5249,5257)"} true;
L19:

    // $t53 := 128 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:161:24+4
    assume {:print "$at(13,5260,5264)"} true;
    $t53 := 128;
    assume $IsValid'u32'($t53);

    // $t54 := &($t5, $t53) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:161:13+15
    call $t54 := $AndBv32($t5, $int2bv.32($t53));

    // $t55 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:161:32+1
    $t55 := 0bv32;
    assume $IsValid'bv32'($t55);

    // $t56 := !=($t54, $t55) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:161:13+20
    $t56 := !$IsEqual'bv32'($t54, $t55);

    // if ($t56) goto L20 else goto L22 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:161:9+121
    if ($t56) { goto L20; } else { goto L22; }

    // label L20 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:162:45+5
    assume {:print "$at(13,5317,5322)"} true;
L20:

    // $t57 := 18329067761203520168 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:162:52+24
    assume {:print "$at(13,5324,5348)"} true;
    $t57 := 18329067761203520168;
    assume $IsValid'u128'($t57);

    // $t58 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:162:78+4
    $t58 := 64;
    assume $IsValid'u8'($t58);

    // $t59 := full_math_u128::mul_shr($t2, $t57, $t58) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:162:21+62
    call $t59 := $aa_full_math_u128_mul_shr($t2, $t57, $t58);
    if ($abort_flag) {
        assume {:print "$at(13,5293,5355)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t59 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:162:13+70
    $t2 := $t59;

    // trace_local[ratio]($t59) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:162:13+70
    assume {:print "$track_local(102,3,2):", $t59} $t59 == $t59;

    // label L22 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:164:13+8
    assume {:print "$at(13,5380,5388)"} true;
L22:

    // $t60 := 256 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:164:24+5
    assume {:print "$at(13,5391,5396)"} true;
    $t60 := 256;
    assume $IsValid'u32'($t60);

    // $t61 := &($t5, $t60) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:164:13+16
    call $t61 := $AndBv32($t5, $int2bv.32($t60));

    // $t62 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:164:33+1
    $t62 := 0bv32;
    assume $IsValid'bv32'($t62);

    // $t63 := !=($t61, $t62) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:164:13+21
    $t63 := !$IsEqual'bv32'($t61, $t62);

    // if ($t63) goto L23 else goto L25 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:164:9+122
    if ($t63) { goto L23; } else { goto L25; }

    // label L23 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:165:45+5
    assume {:print "$at(13,5449,5454)"} true;
L23:

    // $t64 := 18212142134806087854 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:165:52+24
    assume {:print "$at(13,5456,5480)"} true;
    $t64 := 18212142134806087854;
    assume $IsValid'u128'($t64);

    // $t65 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:165:78+4
    $t65 := 64;
    assume $IsValid'u8'($t65);

    // $t66 := full_math_u128::mul_shr($t2, $t64, $t65) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:165:21+62
    call $t66 := $aa_full_math_u128_mul_shr($t2, $t64, $t65);
    if ($abort_flag) {
        assume {:print "$at(13,5425,5487)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t66 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:165:13+70
    $t2 := $t66;

    // trace_local[ratio]($t66) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:165:13+70
    assume {:print "$track_local(102,3,2):", $t66} $t66 == $t66;

    // label L25 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:167:13+8
    assume {:print "$at(13,5512,5520)"} true;
L25:

    // $t67 := 512 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:167:24+5
    assume {:print "$at(13,5523,5528)"} true;
    $t67 := 512;
    assume $IsValid'u32'($t67);

    // $t68 := &($t5, $t67) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:167:13+16
    call $t68 := $AndBv32($t5, $int2bv.32($t67));

    // $t69 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:167:33+1
    $t69 := 0bv32;
    assume $IsValid'bv32'($t69);

    // $t70 := !=($t68, $t69) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:167:13+21
    $t70 := !$IsEqual'bv32'($t68, $t69);

    // if ($t70) goto L26 else goto L28 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:167:9+122
    if ($t70) { goto L26; } else { goto L28; }

    // label L26 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:168:45+5
    assume {:print "$at(13,5581,5586)"} true;
L26:

    // $t71 := 17980523815641551639 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:168:52+24
    assume {:print "$at(13,5588,5612)"} true;
    $t71 := 17980523815641551639;
    assume $IsValid'u128'($t71);

    // $t72 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:168:78+4
    $t72 := 64;
    assume $IsValid'u8'($t72);

    // $t73 := full_math_u128::mul_shr($t2, $t71, $t72) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:168:21+62
    call $t73 := $aa_full_math_u128_mul_shr($t2, $t71, $t72);
    if ($abort_flag) {
        assume {:print "$at(13,5557,5619)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t73 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:168:13+70
    $t2 := $t73;

    // trace_local[ratio]($t73) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:168:13+70
    assume {:print "$track_local(102,3,2):", $t73} $t73 == $t73;

    // label L28 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:170:13+8
    assume {:print "$at(13,5644,5652)"} true;
L28:

    // $t74 := 1024 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:170:24+5
    assume {:print "$at(13,5655,5660)"} true;
    $t74 := 1024;
    assume $IsValid'u32'($t74);

    // $t75 := &($t5, $t74) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:170:13+16
    call $t75 := $AndBv32($t5, $int2bv.32($t74));

    // $t76 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:170:33+1
    $t76 := 0bv32;
    assume $IsValid'bv32'($t76);

    // $t77 := !=($t75, $t76) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:170:13+21
    $t77 := !$IsEqual'bv32'($t75, $t76);

    // if ($t77) goto L29 else goto L31 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:170:9+122
    if ($t77) { goto L29; } else { goto L31; }

    // label L29 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:171:45+5
    assume {:print "$at(13,5713,5718)"} true;
L29:

    // $t78 := 17526086738831147013 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:171:52+24
    assume {:print "$at(13,5720,5744)"} true;
    $t78 := 17526086738831147013;
    assume $IsValid'u128'($t78);

    // $t79 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:171:78+4
    $t79 := 64;
    assume $IsValid'u8'($t79);

    // $t80 := full_math_u128::mul_shr($t2, $t78, $t79) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:171:21+62
    call $t80 := $aa_full_math_u128_mul_shr($t2, $t78, $t79);
    if ($abort_flag) {
        assume {:print "$at(13,5689,5751)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t80 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:171:13+70
    $t2 := $t80;

    // trace_local[ratio]($t80) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:171:13+70
    assume {:print "$track_local(102,3,2):", $t80} $t80 == $t80;

    // label L31 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:173:13+8
    assume {:print "$at(13,5776,5784)"} true;
L31:

    // $t81 := 2048 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:173:24+5
    assume {:print "$at(13,5787,5792)"} true;
    $t81 := 2048;
    assume $IsValid'u32'($t81);

    // $t82 := &($t5, $t81) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:173:13+16
    call $t82 := $AndBv32($t5, $int2bv.32($t81));

    // $t83 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:173:33+1
    $t83 := 0bv32;
    assume $IsValid'bv32'($t83);

    // $t84 := !=($t82, $t83) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:173:13+21
    $t84 := !$IsEqual'bv32'($t82, $t83);

    // if ($t84) goto L32 else goto L34 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:173:9+122
    if ($t84) { goto L32; } else { goto L34; }

    // label L32 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:174:45+5
    assume {:print "$at(13,5845,5850)"} true;
L32:

    // $t85 := 16651378430235024244 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:174:52+24
    assume {:print "$at(13,5852,5876)"} true;
    $t85 := 16651378430235024244;
    assume $IsValid'u128'($t85);

    // $t86 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:174:78+4
    $t86 := 64;
    assume $IsValid'u8'($t86);

    // $t87 := full_math_u128::mul_shr($t2, $t85, $t86) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:174:21+62
    call $t87 := $aa_full_math_u128_mul_shr($t2, $t85, $t86);
    if ($abort_flag) {
        assume {:print "$at(13,5821,5883)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t87 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:174:13+70
    $t2 := $t87;

    // trace_local[ratio]($t87) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:174:13+70
    assume {:print "$track_local(102,3,2):", $t87} $t87 == $t87;

    // label L34 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:176:13+8
    assume {:print "$at(13,5908,5916)"} true;
L34:

    // $t88 := 4096 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:176:24+6
    assume {:print "$at(13,5919,5925)"} true;
    $t88 := 4096;
    assume $IsValid'u32'($t88);

    // $t89 := &($t5, $t88) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:176:13+17
    call $t89 := $AndBv32($t5, $int2bv.32($t88));

    // $t90 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:176:34+1
    $t90 := 0bv32;
    assume $IsValid'bv32'($t90);

    // $t91 := !=($t89, $t90) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:176:13+22
    $t91 := !$IsEqual'bv32'($t89, $t90);

    // if ($t91) goto L35 else goto L37 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:176:9+123
    if ($t91) { goto L35; } else { goto L37; }

    // label L35 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:177:45+5
    assume {:print "$at(13,5978,5983)"} true;
L35:

    // $t92 := 15030750278693429944 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:177:52+24
    assume {:print "$at(13,5985,6009)"} true;
    $t92 := 15030750278693429944;
    assume $IsValid'u128'($t92);

    // $t93 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:177:78+4
    $t93 := 64;
    assume $IsValid'u8'($t93);

    // $t94 := full_math_u128::mul_shr($t2, $t92, $t93) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:177:21+62
    call $t94 := $aa_full_math_u128_mul_shr($t2, $t92, $t93);
    if ($abort_flag) {
        assume {:print "$at(13,5954,6016)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t94 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:177:13+70
    $t2 := $t94;

    // trace_local[ratio]($t94) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:177:13+70
    assume {:print "$track_local(102,3,2):", $t94} $t94 == $t94;

    // label L37 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:179:13+8
    assume {:print "$at(13,6041,6049)"} true;
L37:

    // $t95 := 8192 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:179:24+6
    assume {:print "$at(13,6052,6058)"} true;
    $t95 := 8192;
    assume $IsValid'u32'($t95);

    // $t96 := &($t5, $t95) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:179:13+17
    call $t96 := $AndBv32($t5, $int2bv.32($t95));

    // $t97 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:179:34+1
    $t97 := 0bv32;
    assume $IsValid'bv32'($t97);

    // $t98 := !=($t96, $t97) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:179:13+22
    $t98 := !$IsEqual'bv32'($t96, $t97);

    // if ($t98) goto L38 else goto L40 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:179:9+123
    if ($t98) { goto L38; } else { goto L40; }

    // label L38 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:180:45+5
    assume {:print "$at(13,6111,6116)"} true;
L38:

    // $t99 := 12247334978882834399 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:180:52+24
    assume {:print "$at(13,6118,6142)"} true;
    $t99 := 12247334978882834399;
    assume $IsValid'u128'($t99);

    // $t100 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:180:78+4
    $t100 := 64;
    assume $IsValid'u8'($t100);

    // $t101 := full_math_u128::mul_shr($t2, $t99, $t100) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:180:21+62
    call $t101 := $aa_full_math_u128_mul_shr($t2, $t99, $t100);
    if ($abort_flag) {
        assume {:print "$at(13,6087,6149)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t101 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:180:13+70
    $t2 := $t101;

    // trace_local[ratio]($t101) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:180:13+70
    assume {:print "$track_local(102,3,2):", $t101} $t101 == $t101;

    // label L40 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:182:13+8
    assume {:print "$at(13,6174,6182)"} true;
L40:

    // $t102 := 16384 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:182:24+6
    assume {:print "$at(13,6185,6191)"} true;
    $t102 := 16384;
    assume $IsValid'u32'($t102);

    // $t103 := &($t5, $t102) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:182:13+17
    call $t103 := $AndBv32($t5, $int2bv.32($t102));

    // $t104 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:182:34+1
    $t104 := 0bv32;
    assume $IsValid'bv32'($t104);

    // $t105 := !=($t103, $t104) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:182:13+22
    $t105 := !$IsEqual'bv32'($t103, $t104);

    // if ($t105) goto L41 else goto L43 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:182:9+122
    if ($t105) { goto L41; } else { goto L43; }

    // label L41 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:183:45+5
    assume {:print "$at(13,6244,6249)"} true;
L41:

    // $t106 := 8131365268884726200 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:183:52+23
    assume {:print "$at(13,6251,6274)"} true;
    $t106 := 8131365268884726200;
    assume $IsValid'u128'($t106);

    // $t107 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:183:77+4
    $t107 := 64;
    assume $IsValid'u8'($t107);

    // $t108 := full_math_u128::mul_shr($t2, $t106, $t107) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:183:21+61
    call $t108 := $aa_full_math_u128_mul_shr($t2, $t106, $t107);
    if ($abort_flag) {
        assume {:print "$at(13,6220,6281)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t108 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:183:13+69
    $t2 := $t108;

    // trace_local[ratio]($t108) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:183:13+69
    assume {:print "$track_local(102,3,2):", $t108} $t108 == $t108;

    // label L43 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:185:13+8
    assume {:print "$at(13,6306,6314)"} true;
L43:

    // $t109 := 32768 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:185:24+6
    assume {:print "$at(13,6317,6323)"} true;
    $t109 := 32768;
    assume $IsValid'u32'($t109);

    // $t110 := &($t5, $t109) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:185:13+17
    call $t110 := $AndBv32($t5, $int2bv.32($t109));

    // $t111 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:185:34+1
    $t111 := 0bv32;
    assume $IsValid'bv32'($t111);

    // $t112 := !=($t110, $t111) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:185:13+22
    $t112 := !$IsEqual'bv32'($t110, $t111);

    // if ($t112) goto L44 else goto L46 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:185:9+122
    if ($t112) { goto L44; } else { goto L46; }

    // label L44 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:186:45+5
    assume {:print "$at(13,6376,6381)"} true;
L44:

    // $t113 := 3584323654723342297 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:186:52+23
    assume {:print "$at(13,6383,6406)"} true;
    $t113 := 3584323654723342297;
    assume $IsValid'u128'($t113);

    // $t114 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:186:77+4
    $t114 := 64;
    assume $IsValid'u8'($t114);

    // $t115 := full_math_u128::mul_shr($t2, $t113, $t114) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:186:21+61
    call $t115 := $aa_full_math_u128_mul_shr($t2, $t113, $t114);
    if ($abort_flag) {
        assume {:print "$at(13,6352,6413)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t115 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:186:13+69
    $t2 := $t115;

    // trace_local[ratio]($t115) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:186:13+69
    assume {:print "$track_local(102,3,2):", $t115} $t115 == $t115;

    // label L46 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:188:13+8
    assume {:print "$at(13,6438,6446)"} true;
L46:

    // $t116 := 65536 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:188:24+7
    assume {:print "$at(13,6449,6456)"} true;
    $t116 := 65536;
    assume $IsValid'u32'($t116);

    // $t117 := &($t5, $t116) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:188:13+18
    call $t117 := $AndBv32($t5, $int2bv.32($t116));

    // $t118 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:188:35+1
    $t118 := 0bv32;
    assume $IsValid'bv32'($t118);

    // $t119 := !=($t117, $t118) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:188:13+23
    $t119 := !$IsEqual'bv32'($t117, $t118);

    // if ($t119) goto L47 else goto L49 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:188:9+122
    if ($t119) { goto L47; } else { goto L49; }

    // label L47 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:189:45+5
    assume {:print "$at(13,6509,6514)"} true;
L47:

    // $t120 := 696457651847595233 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:189:52+22
    assume {:print "$at(13,6516,6538)"} true;
    $t120 := 696457651847595233;
    assume $IsValid'u128'($t120);

    // $t121 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:189:76+4
    $t121 := 64;
    assume $IsValid'u8'($t121);

    // $t122 := full_math_u128::mul_shr($t2, $t120, $t121) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:189:21+60
    call $t122 := $aa_full_math_u128_mul_shr($t2, $t120, $t121);
    if ($abort_flag) {
        assume {:print "$at(13,6485,6545)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t122 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:189:13+68
    $t2 := $t122;

    // trace_local[ratio]($t122) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:189:13+68
    assume {:print "$track_local(102,3,2):", $t122} $t122 == $t122;

    // label L49 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:191:13+8
    assume {:print "$at(13,6570,6578)"} true;
L49:

    // $t123 := 131072 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:191:24+7
    assume {:print "$at(13,6581,6588)"} true;
    $t123 := 131072;
    assume $IsValid'u32'($t123);

    // $t124 := &($t5, $t123) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:191:13+18
    call $t124 := $AndBv32($t5, $int2bv.32($t123));

    // $t125 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:191:35+1
    $t125 := 0bv32;
    assume $IsValid'bv32'($t125);

    // $t126 := !=($t124, $t125) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:191:13+23
    $t126 := !$IsEqual'bv32'($t124, $t125);

    // if ($t126) goto L50 else goto L52 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:191:9+121
    if ($t126) { goto L50; } else { goto L52; }

    // label L50 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:192:45+5
    assume {:print "$at(13,6641,6646)"} true;
L50:

    // $t127 := 26294789957452057 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:192:52+21
    assume {:print "$at(13,6648,6669)"} true;
    $t127 := 26294789957452057;
    assume $IsValid'u128'($t127);

    // $t128 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:192:75+4
    $t128 := 64;
    assume $IsValid'u8'($t128);

    // $t129 := full_math_u128::mul_shr($t2, $t127, $t128) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:192:21+59
    call $t129 := $aa_full_math_u128_mul_shr($t2, $t127, $t128);
    if ($abort_flag) {
        assume {:print "$at(13,6617,6676)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t129 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:192:13+67
    $t2 := $t129;

    // trace_local[ratio]($t129) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:192:13+67
    assume {:print "$track_local(102,3,2):", $t129} $t129 == $t129;

    // label L52 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:194:13+8
    assume {:print "$at(13,6701,6709)"} true;
L52:

    // $t130 := 262144 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:194:24+7
    assume {:print "$at(13,6712,6719)"} true;
    $t130 := 262144;
    assume $IsValid'u32'($t130);

    // $t131 := &($t5, $t130) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:194:13+18
    call $t131 := $AndBv32($t5, $int2bv.32($t130));

    // $t132 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:194:35+1
    $t132 := 0bv32;
    assume $IsValid'bv32'($t132);

    // $t133 := !=($t131, $t132) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:194:13+23
    $t133 := !$IsEqual'bv32'($t131, $t132);

    // if ($t133) goto L53 else goto L55 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:194:9+118
    if ($t133) { goto L53; } else { goto L55; }

    // label L53 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:195:45+5
    assume {:print "$at(13,6772,6777)"} true;
L53:

    // $t134 := 37481735321082 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:195:52+18
    assume {:print "$at(13,6779,6797)"} true;
    $t134 := 37481735321082;
    assume $IsValid'u128'($t134);

    // $t135 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:195:72+4
    $t135 := 64;
    assume $IsValid'u8'($t135);

    // $t136 := full_math_u128::mul_shr($t2, $t134, $t135) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:195:21+56
    call $t136 := $aa_full_math_u128_mul_shr($t2, $t134, $t135);
    if ($abort_flag) {
        assume {:print "$at(13,6748,6804)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,3):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t136 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:195:13+64
    $t2 := $t136;

    // trace_local[ratio]($t136) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:195:13+64
    assume {:print "$track_local(102,3,2):", $t136} $t136 == $t136;

    // label L55 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:198:9+5
    assume {:print "$at(13,6826,6831)"} true;
L55:

    // trace_return[0]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:136:63+2585
    assume {:print "$at(13,4252,6837)"} true;
    assume {:print "$track_return(102,3,0):", $t2} $t2 == $t2;

    // goto L57 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:136:63+2585
    goto L57;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:141:13+24
    assume {:print "$at(13,4419,4443)"} true;
L0:

    // $t137 := 18446744073709551616 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:141:13+24
    assume {:print "$at(13,4419,4443)"} true;
    $t137 := 18446744073709551616;
    assume $IsValid'u128'($t137);

    // $t2 := $t137 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:141:13+24
    $t2 := $t137;

    // trace_local[ratio]($t137) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:141:13+24
    assume {:print "$track_local(102,3,2):", $t137} $t137 == $t137;

    // goto L56 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:141:13+24
    goto L56;

    // label L57 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:199:5+1
    assume {:print "$at(13,6836,6837)"} true;
L57:

    // return $t2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:199:5+1
    assume {:print "$at(13,6836,6837)"} true;
    $ret0 := $t2;
    return;

    // label L58 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:199:5+1
L58:

    // abort($t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:199:5+1
    assume {:print "$at(13,6836,6837)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun tick_math::get_sqrt_price_at_positive_tick [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:201:5+2840
procedure {:inline 1} $aa_tick_math_get_sqrt_price_at_positive_tick(_$t0: $aa_i32_I32) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: $aa_i32_I32;
    var $t4: int;
    var $t5: bv32;
    var $t6: int;
    var $t7: bv32;
    var $t8: bv32;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t12: bv32;
    var $t13: bv32;
    var $t14: bool;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: bv32;
    var $t20: bv32;
    var $t21: bool;
    var $t22: int;
    var $t23: int;
    var $t24: int;
    var $t25: int;
    var $t26: bv32;
    var $t27: bv32;
    var $t28: bool;
    var $t29: int;
    var $t30: int;
    var $t31: int;
    var $t32: int;
    var $t33: bv32;
    var $t34: bv32;
    var $t35: bool;
    var $t36: int;
    var $t37: int;
    var $t38: int;
    var $t39: int;
    var $t40: bv32;
    var $t41: bv32;
    var $t42: bool;
    var $t43: int;
    var $t44: int;
    var $t45: int;
    var $t46: int;
    var $t47: bv32;
    var $t48: bv32;
    var $t49: bool;
    var $t50: int;
    var $t51: int;
    var $t52: int;
    var $t53: int;
    var $t54: bv32;
    var $t55: bv32;
    var $t56: bool;
    var $t57: int;
    var $t58: int;
    var $t59: int;
    var $t60: int;
    var $t61: bv32;
    var $t62: bv32;
    var $t63: bool;
    var $t64: int;
    var $t65: int;
    var $t66: int;
    var $t67: int;
    var $t68: bv32;
    var $t69: bv32;
    var $t70: bool;
    var $t71: int;
    var $t72: int;
    var $t73: int;
    var $t74: int;
    var $t75: bv32;
    var $t76: bv32;
    var $t77: bool;
    var $t78: int;
    var $t79: int;
    var $t80: int;
    var $t81: int;
    var $t82: bv32;
    var $t83: bv32;
    var $t84: bool;
    var $t85: int;
    var $t86: int;
    var $t87: int;
    var $t88: int;
    var $t89: bv32;
    var $t90: bv32;
    var $t91: bool;
    var $t92: int;
    var $t93: int;
    var $t94: int;
    var $t95: int;
    var $t96: bv32;
    var $t97: bv32;
    var $t98: bool;
    var $t99: int;
    var $t100: int;
    var $t101: int;
    var $t102: int;
    var $t103: bv32;
    var $t104: bv32;
    var $t105: bool;
    var $t106: int;
    var $t107: int;
    var $t108: int;
    var $t109: int;
    var $t110: bv32;
    var $t111: bv32;
    var $t112: bool;
    var $t113: int;
    var $t114: int;
    var $t115: int;
    var $t116: int;
    var $t117: bv32;
    var $t118: bv32;
    var $t119: bool;
    var $t120: int;
    var $t121: int;
    var $t122: int;
    var $t123: int;
    var $t124: bv32;
    var $t125: bv32;
    var $t126: bool;
    var $t127: int;
    var $t128: int;
    var $t129: int;
    var $t130: int;
    var $t131: bv32;
    var $t132: bv32;
    var $t133: bool;
    var $t134: int;
    var $t135: int;
    var $t136: int;
    var $t137: int;
    var $t138: int;
    var $t139: int;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'u128': int;
    var $temp_0'bv32': bv32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[tick]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:201:5+1
    assume {:print "$at(13,6843,6844)"} true;
    assume {:print "$track_local(102,4,0):", $t0} $t0 == $t0;

    // $t3 := i32::abs($t0) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:202:36+14
    assume {:print "$at(13,6938,6952)"} true;
    call $t3 := $aa_i32_abs($t0);
    if ($abort_flag) {
        assume {:print "$at(13,6938,6952)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t5 := i32::as_u32($t3) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:202:24+27
    call $t5 := $aa_i32_as_u32($t3);
    if ($abort_flag) {
        assume {:print "$at(13,6926,6953)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // trace_local[abs_tick]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:202:24+27
    assume {:print "$track_local(102,4,1):", $t5} $t5 == $t5;

    // $t6 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:203:36+3
    assume {:print "$at(13,6990,6993)"} true;
    $t6 := 1;
    assume $IsValid'u32'($t6);

    // $t7 := &($t5, $t6) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:203:25+14
    call $t7 := $AndBv32($t5, $int2bv.32($t6));

    // $t8 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:203:43+1
    $t8 := 0bv32;
    assume $IsValid'bv32'($t8);

    // $t9 := !=($t7, $t8) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:203:25+19
    $t9 := !$IsEqual'bv32'($t7, $t8);

    // if ($t9) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:203:21+145
    if ($t9) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:204:13+33
    assume {:print "$at(13,7014,7047)"} true;
L1:

    // $t10 := 79232123823359799118286999567 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:204:13+33
    assume {:print "$at(13,7014,7047)"} true;
    $t10 := 79232123823359799118286999567;
    assume $IsValid'u128'($t10);

    // $t2 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:204:13+33
    $t2 := $t10;

    // trace_local[ratio]($t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:204:13+33
    assume {:print "$track_local(102,4,2):", $t10} $t10 == $t10;

    // label L56 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:209:13+8
    assume {:print "$at(13,7135,7143)"} true;
L56:

    // $t11 := 2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:209:24+3
    assume {:print "$at(13,7146,7149)"} true;
    $t11 := 2;
    assume $IsValid'u32'($t11);

    // $t12 := &($t5, $t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:209:13+14
    call $t12 := $AndBv32($t5, $int2bv.32($t11));

    // $t13 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:209:31+1
    $t13 := 0bv32;
    assume $IsValid'bv32'($t13);

    // $t14 := !=($t12, $t13) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:209:13+19
    $t14 := !$IsEqual'bv32'($t12, $t13);

    // if ($t14) goto L2 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:209:9+128
    if ($t14) { goto L2; } else { goto L4; }

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:210:45+5
    assume {:print "$at(13,7202,7207)"} true;
L2:

    // $t15 := 79236085330515764027303304731 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:210:52+33
    assume {:print "$at(13,7209,7242)"} true;
    $t15 := 79236085330515764027303304731;
    assume $IsValid'u128'($t15);

    // $t16 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:210:87+4
    $t16 := 96;
    assume $IsValid'u8'($t16);

    // $t17 := full_math_u128::mul_shr($t2, $t15, $t16) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:210:21+71
    call $t17 := $aa_full_math_u128_mul_shr($t2, $t15, $t16);
    if ($abort_flag) {
        assume {:print "$at(13,7178,7249)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:210:13+79
    $t2 := $t17;

    // trace_local[ratio]($t17) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:210:13+79
    assume {:print "$track_local(102,4,2):", $t17} $t17 == $t17;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:212:13+8
    assume {:print "$at(13,7273,7281)"} true;
L4:

    // $t18 := 4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:212:24+3
    assume {:print "$at(13,7284,7287)"} true;
    $t18 := 4;
    assume $IsValid'u32'($t18);

    // $t19 := &($t5, $t18) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:212:13+14
    call $t19 := $AndBv32($t5, $int2bv.32($t18));

    // $t20 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:212:31+1
    $t20 := 0bv32;
    assume $IsValid'bv32'($t20);

    // $t21 := !=($t19, $t20) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:212:13+19
    $t21 := !$IsEqual'bv32'($t19, $t20);

    // if ($t21) goto L5 else goto L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:212:9+128
    if ($t21) { goto L5; } else { goto L7; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:213:45+5
    assume {:print "$at(13,7340,7345)"} true;
L5:

    // $t22 := 79244008939048815603706035061 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:213:52+33
    assume {:print "$at(13,7347,7380)"} true;
    $t22 := 79244008939048815603706035061;
    assume $IsValid'u128'($t22);

    // $t23 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:213:87+4
    $t23 := 96;
    assume $IsValid'u8'($t23);

    // $t24 := full_math_u128::mul_shr($t2, $t22, $t23) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:213:21+71
    call $t24 := $aa_full_math_u128_mul_shr($t2, $t22, $t23);
    if ($abort_flag) {
        assume {:print "$at(13,7316,7387)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t24 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:213:13+79
    $t2 := $t24;

    // trace_local[ratio]($t24) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:213:13+79
    assume {:print "$track_local(102,4,2):", $t24} $t24 == $t24;

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:215:13+8
    assume {:print "$at(13,7411,7419)"} true;
L7:

    // $t25 := 8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:215:24+3
    assume {:print "$at(13,7422,7425)"} true;
    $t25 := 8;
    assume $IsValid'u32'($t25);

    // $t26 := &($t5, $t25) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:215:13+14
    call $t26 := $AndBv32($t5, $int2bv.32($t25));

    // $t27 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:215:31+1
    $t27 := 0bv32;
    assume $IsValid'bv32'($t27);

    // $t28 := !=($t26, $t27) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:215:13+19
    $t28 := !$IsEqual'bv32'($t26, $t27);

    // if ($t28) goto L8 else goto L10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:215:9+128
    if ($t28) { goto L8; } else { goto L10; }

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:216:45+5
    assume {:print "$at(13,7478,7483)"} true;
L8:

    // $t29 := 79259858533276714757314932305 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:216:52+33
    assume {:print "$at(13,7485,7518)"} true;
    $t29 := 79259858533276714757314932305;
    assume $IsValid'u128'($t29);

    // $t30 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:216:87+4
    $t30 := 96;
    assume $IsValid'u8'($t30);

    // $t31 := full_math_u128::mul_shr($t2, $t29, $t30) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:216:21+71
    call $t31 := $aa_full_math_u128_mul_shr($t2, $t29, $t30);
    if ($abort_flag) {
        assume {:print "$at(13,7454,7525)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t31 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:216:13+79
    $t2 := $t31;

    // trace_local[ratio]($t31) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:216:13+79
    assume {:print "$track_local(102,4,2):", $t31} $t31 == $t31;

    // label L10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:218:13+8
    assume {:print "$at(13,7549,7557)"} true;
L10:

    // $t32 := 16 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:218:24+4
    assume {:print "$at(13,7560,7564)"} true;
    $t32 := 16;
    assume $IsValid'u32'($t32);

    // $t33 := &($t5, $t32) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:218:13+15
    call $t33 := $AndBv32($t5, $int2bv.32($t32));

    // $t34 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:218:32+1
    $t34 := 0bv32;
    assume $IsValid'bv32'($t34);

    // $t35 := !=($t33, $t34) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:218:13+20
    $t35 := !$IsEqual'bv32'($t33, $t34);

    // if ($t35) goto L11 else goto L13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:218:9+129
    if ($t35) { goto L11; } else { goto L13; }

    // label L11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:219:45+5
    assume {:print "$at(13,7617,7622)"} true;
L11:

    // $t36 := 79291567232598584799939703904 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:219:52+33
    assume {:print "$at(13,7624,7657)"} true;
    $t36 := 79291567232598584799939703904;
    assume $IsValid'u128'($t36);

    // $t37 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:219:87+4
    $t37 := 96;
    assume $IsValid'u8'($t37);

    // $t38 := full_math_u128::mul_shr($t2, $t36, $t37) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:219:21+71
    call $t38 := $aa_full_math_u128_mul_shr($t2, $t36, $t37);
    if ($abort_flag) {
        assume {:print "$at(13,7593,7664)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t38 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:219:13+79
    $t2 := $t38;

    // trace_local[ratio]($t38) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:219:13+79
    assume {:print "$track_local(102,4,2):", $t38} $t38 == $t38;

    // label L13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:221:13+8
    assume {:print "$at(13,7688,7696)"} true;
L13:

    // $t39 := 32 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:221:24+4
    assume {:print "$at(13,7699,7703)"} true;
    $t39 := 32;
    assume $IsValid'u32'($t39);

    // $t40 := &($t5, $t39) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:221:13+15
    call $t40 := $AndBv32($t5, $int2bv.32($t39));

    // $t41 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:221:32+1
    $t41 := 0bv32;
    assume $IsValid'bv32'($t41);

    // $t42 := !=($t40, $t41) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:221:13+20
    $t42 := !$IsEqual'bv32'($t40, $t41);

    // if ($t42) goto L14 else goto L16 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:221:9+129
    if ($t42) { goto L14; } else { goto L16; }

    // label L14 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:222:45+5
    assume {:print "$at(13,7756,7761)"} true;
L14:

    // $t43 := 79355022692464371645785046466 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:222:52+33
    assume {:print "$at(13,7763,7796)"} true;
    $t43 := 79355022692464371645785046466;
    assume $IsValid'u128'($t43);

    // $t44 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:222:87+4
    $t44 := 96;
    assume $IsValid'u8'($t44);

    // $t45 := full_math_u128::mul_shr($t2, $t43, $t44) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:222:21+71
    call $t45 := $aa_full_math_u128_mul_shr($t2, $t43, $t44);
    if ($abort_flag) {
        assume {:print "$at(13,7732,7803)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t45 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:222:13+79
    $t2 := $t45;

    // trace_local[ratio]($t45) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:222:13+79
    assume {:print "$track_local(102,4,2):", $t45} $t45 == $t45;

    // label L16 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:224:13+8
    assume {:print "$at(13,7827,7835)"} true;
L16:

    // $t46 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:224:24+4
    assume {:print "$at(13,7838,7842)"} true;
    $t46 := 64;
    assume $IsValid'u32'($t46);

    // $t47 := &($t5, $t46) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:224:13+15
    call $t47 := $AndBv32($t5, $int2bv.32($t46));

    // $t48 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:224:32+1
    $t48 := 0bv32;
    assume $IsValid'bv32'($t48);

    // $t49 := !=($t47, $t48) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:224:13+20
    $t49 := !$IsEqual'bv32'($t47, $t48);

    // if ($t49) goto L17 else goto L19 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:224:9+129
    if ($t49) { goto L17; } else { goto L19; }

    // label L17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:225:45+5
    assume {:print "$at(13,7895,7900)"} true;
L17:

    // $t50 := 79482085999252804386437311141 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:225:52+33
    assume {:print "$at(13,7902,7935)"} true;
    $t50 := 79482085999252804386437311141;
    assume $IsValid'u128'($t50);

    // $t51 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:225:87+4
    $t51 := 96;
    assume $IsValid'u8'($t51);

    // $t52 := full_math_u128::mul_shr($t2, $t50, $t51) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:225:21+71
    call $t52 := $aa_full_math_u128_mul_shr($t2, $t50, $t51);
    if ($abort_flag) {
        assume {:print "$at(13,7871,7942)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t52 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:225:13+79
    $t2 := $t52;

    // trace_local[ratio]($t52) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:225:13+79
    assume {:print "$track_local(102,4,2):", $t52} $t52 == $t52;

    // label L19 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:227:13+8
    assume {:print "$at(13,7966,7974)"} true;
L19:

    // $t53 := 128 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:227:24+4
    assume {:print "$at(13,7977,7981)"} true;
    $t53 := 128;
    assume $IsValid'u32'($t53);

    // $t54 := &($t5, $t53) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:227:13+15
    call $t54 := $AndBv32($t5, $int2bv.32($t53));

    // $t55 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:227:32+1
    $t55 := 0bv32;
    assume $IsValid'bv32'($t55);

    // $t56 := !=($t54, $t55) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:227:13+20
    $t56 := !$IsEqual'bv32'($t54, $t55);

    // if ($t56) goto L20 else goto L22 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:227:9+129
    if ($t56) { goto L20; } else { goto L22; }

    // label L20 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:228:45+5
    assume {:print "$at(13,8034,8039)"} true;
L20:

    // $t57 := 79736823300114093921829183326 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:228:52+33
    assume {:print "$at(13,8041,8074)"} true;
    $t57 := 79736823300114093921829183326;
    assume $IsValid'u128'($t57);

    // $t58 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:228:87+4
    $t58 := 96;
    assume $IsValid'u8'($t58);

    // $t59 := full_math_u128::mul_shr($t2, $t57, $t58) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:228:21+71
    call $t59 := $aa_full_math_u128_mul_shr($t2, $t57, $t58);
    if ($abort_flag) {
        assume {:print "$at(13,8010,8081)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t59 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:228:13+79
    $t2 := $t59;

    // trace_local[ratio]($t59) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:228:13+79
    assume {:print "$track_local(102,4,2):", $t59} $t59 == $t59;

    // label L22 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:230:13+8
    assume {:print "$at(13,8105,8113)"} true;
L22:

    // $t60 := 256 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:230:24+5
    assume {:print "$at(13,8116,8121)"} true;
    $t60 := 256;
    assume $IsValid'u32'($t60);

    // $t61 := &($t5, $t60) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:230:13+16
    call $t61 := $AndBv32($t5, $int2bv.32($t60));

    // $t62 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:230:33+1
    $t62 := 0bv32;
    assume $IsValid'bv32'($t62);

    // $t63 := !=($t61, $t62) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:230:13+21
    $t63 := !$IsEqual'bv32'($t61, $t62);

    // if ($t63) goto L23 else goto L25 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:230:9+130
    if ($t63) { goto L23; } else { goto L25; }

    // label L23 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:231:45+5
    assume {:print "$at(13,8174,8179)"} true;
L23:

    // $t64 := 80248749790819932309965073892 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:231:52+33
    assume {:print "$at(13,8181,8214)"} true;
    $t64 := 80248749790819932309965073892;
    assume $IsValid'u128'($t64);

    // $t65 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:231:87+4
    $t65 := 96;
    assume $IsValid'u8'($t65);

    // $t66 := full_math_u128::mul_shr($t2, $t64, $t65) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:231:21+71
    call $t66 := $aa_full_math_u128_mul_shr($t2, $t64, $t65);
    if ($abort_flag) {
        assume {:print "$at(13,8150,8221)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t66 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:231:13+79
    $t2 := $t66;

    // trace_local[ratio]($t66) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:231:13+79
    assume {:print "$track_local(102,4,2):", $t66} $t66 == $t66;

    // label L25 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:233:13+8
    assume {:print "$at(13,8245,8253)"} true;
L25:

    // $t67 := 512 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:233:24+5
    assume {:print "$at(13,8256,8261)"} true;
    $t67 := 512;
    assume $IsValid'u32'($t67);

    // $t68 := &($t5, $t67) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:233:13+16
    call $t68 := $AndBv32($t5, $int2bv.32($t67));

    // $t69 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:233:33+1
    $t69 := 0bv32;
    assume $IsValid'bv32'($t69);

    // $t70 := !=($t68, $t69) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:233:13+21
    $t70 := !$IsEqual'bv32'($t68, $t69);

    // if ($t70) goto L26 else goto L28 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:233:9+130
    if ($t70) { goto L26; } else { goto L28; }

    // label L26 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:234:45+5
    assume {:print "$at(13,8314,8319)"} true;
L26:

    // $t71 := 81282483887344747381513967011 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:234:52+33
    assume {:print "$at(13,8321,8354)"} true;
    $t71 := 81282483887344747381513967011;
    assume $IsValid'u128'($t71);

    // $t72 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:234:87+4
    $t72 := 96;
    assume $IsValid'u8'($t72);

    // $t73 := full_math_u128::mul_shr($t2, $t71, $t72) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:234:21+71
    call $t73 := $aa_full_math_u128_mul_shr($t2, $t71, $t72);
    if ($abort_flag) {
        assume {:print "$at(13,8290,8361)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t73 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:234:13+79
    $t2 := $t73;

    // trace_local[ratio]($t73) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:234:13+79
    assume {:print "$track_local(102,4,2):", $t73} $t73 == $t73;

    // label L28 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:236:13+8
    assume {:print "$at(13,8385,8393)"} true;
L28:

    // $t74 := 1024 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:236:24+5
    assume {:print "$at(13,8396,8401)"} true;
    $t74 := 1024;
    assume $IsValid'u32'($t74);

    // $t75 := &($t5, $t74) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:236:13+16
    call $t75 := $AndBv32($t5, $int2bv.32($t74));

    // $t76 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:236:33+1
    $t76 := 0bv32;
    assume $IsValid'bv32'($t76);

    // $t77 := !=($t75, $t76) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:236:13+21
    $t77 := !$IsEqual'bv32'($t75, $t76);

    // if ($t77) goto L29 else goto L31 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:236:9+130
    if ($t77) { goto L29; } else { goto L31; }

    // label L29 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:237:45+5
    assume {:print "$at(13,8454,8459)"} true;
L29:

    // $t78 := 83390072131320151908154831281 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:237:52+33
    assume {:print "$at(13,8461,8494)"} true;
    $t78 := 83390072131320151908154831281;
    assume $IsValid'u128'($t78);

    // $t79 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:237:87+4
    $t79 := 96;
    assume $IsValid'u8'($t79);

    // $t80 := full_math_u128::mul_shr($t2, $t78, $t79) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:237:21+71
    call $t80 := $aa_full_math_u128_mul_shr($t2, $t78, $t79);
    if ($abort_flag) {
        assume {:print "$at(13,8430,8501)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t80 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:237:13+79
    $t2 := $t80;

    // trace_local[ratio]($t80) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:237:13+79
    assume {:print "$track_local(102,4,2):", $t80} $t80 == $t80;

    // label L31 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:239:13+8
    assume {:print "$at(13,8525,8533)"} true;
L31:

    // $t81 := 2048 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:239:24+5
    assume {:print "$at(13,8536,8541)"} true;
    $t81 := 2048;
    assume $IsValid'u32'($t81);

    // $t82 := &($t5, $t81) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:239:13+16
    call $t82 := $AndBv32($t5, $int2bv.32($t81));

    // $t83 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:239:33+1
    $t83 := 0bv32;
    assume $IsValid'bv32'($t83);

    // $t84 := !=($t82, $t83) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:239:13+21
    $t84 := !$IsEqual'bv32'($t82, $t83);

    // if ($t84) goto L32 else goto L34 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:239:9+130
    if ($t84) { goto L32; } else { goto L34; }

    // label L32 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:240:45+5
    assume {:print "$at(13,8594,8599)"} true;
L32:

    // $t85 := 87770609709833776024991924138 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:240:52+33
    assume {:print "$at(13,8601,8634)"} true;
    $t85 := 87770609709833776024991924138;
    assume $IsValid'u128'($t85);

    // $t86 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:240:87+4
    $t86 := 96;
    assume $IsValid'u8'($t86);

    // $t87 := full_math_u128::mul_shr($t2, $t85, $t86) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:240:21+71
    call $t87 := $aa_full_math_u128_mul_shr($t2, $t85, $t86);
    if ($abort_flag) {
        assume {:print "$at(13,8570,8641)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t87 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:240:13+79
    $t2 := $t87;

    // trace_local[ratio]($t87) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:240:13+79
    assume {:print "$track_local(102,4,2):", $t87} $t87 == $t87;

    // label L34 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:242:13+8
    assume {:print "$at(13,8665,8673)"} true;
L34:

    // $t88 := 4096 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:242:24+6
    assume {:print "$at(13,8676,8682)"} true;
    $t88 := 4096;
    assume $IsValid'u32'($t88);

    // $t89 := &($t5, $t88) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:242:13+17
    call $t89 := $AndBv32($t5, $int2bv.32($t88));

    // $t90 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:242:34+1
    $t90 := 0bv32;
    assume $IsValid'bv32'($t90);

    // $t91 := !=($t89, $t90) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:242:13+22
    $t91 := !$IsEqual'bv32'($t89, $t90);

    // if ($t91) goto L35 else goto L37 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:242:9+131
    if ($t91) { goto L35; } else { goto L37; }

    // label L35 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:243:45+5
    assume {:print "$at(13,8735,8740)"} true;
L35:

    // $t92 := 97234110755111693312479820773 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:243:52+33
    assume {:print "$at(13,8742,8775)"} true;
    $t92 := 97234110755111693312479820773;
    assume $IsValid'u128'($t92);

    // $t93 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:243:87+4
    $t93 := 96;
    assume $IsValid'u8'($t93);

    // $t94 := full_math_u128::mul_shr($t2, $t92, $t93) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:243:21+71
    call $t94 := $aa_full_math_u128_mul_shr($t2, $t92, $t93);
    if ($abort_flag) {
        assume {:print "$at(13,8711,8782)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t94 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:243:13+79
    $t2 := $t94;

    // trace_local[ratio]($t94) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:243:13+79
    assume {:print "$track_local(102,4,2):", $t94} $t94 == $t94;

    // label L37 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:245:13+8
    assume {:print "$at(13,8806,8814)"} true;
L37:

    // $t95 := 8192 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:245:24+6
    assume {:print "$at(13,8817,8823)"} true;
    $t95 := 8192;
    assume $IsValid'u32'($t95);

    // $t96 := &($t5, $t95) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:245:13+17
    call $t96 := $AndBv32($t5, $int2bv.32($t95));

    // $t97 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:245:34+1
    $t97 := 0bv32;
    assume $IsValid'bv32'($t97);

    // $t98 := !=($t96, $t97) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:245:13+22
    $t98 := !$IsEqual'bv32'($t96, $t97);

    // if ($t98) goto L38 else goto L40 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:245:9+132
    if ($t98) { goto L38; } else { goto L40; }

    // label L38 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:246:45+5
    assume {:print "$at(13,8876,8881)"} true;
L38:

    // $t99 := 119332217159966728226237229890 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:246:52+34
    assume {:print "$at(13,8883,8917)"} true;
    $t99 := 119332217159966728226237229890;
    assume $IsValid'u128'($t99);

    // $t100 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:246:88+4
    $t100 := 96;
    assume $IsValid'u8'($t100);

    // $t101 := full_math_u128::mul_shr($t2, $t99, $t100) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:246:21+72
    call $t101 := $aa_full_math_u128_mul_shr($t2, $t99, $t100);
    if ($abort_flag) {
        assume {:print "$at(13,8852,8924)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t101 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:246:13+80
    $t2 := $t101;

    // trace_local[ratio]($t101) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:246:13+80
    assume {:print "$track_local(102,4,2):", $t101} $t101 == $t101;

    // label L40 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:248:13+8
    assume {:print "$at(13,8948,8956)"} true;
L40:

    // $t102 := 16384 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:248:24+6
    assume {:print "$at(13,8959,8965)"} true;
    $t102 := 16384;
    assume $IsValid'u32'($t102);

    // $t103 := &($t5, $t102) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:248:13+17
    call $t103 := $AndBv32($t5, $int2bv.32($t102));

    // $t104 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:248:34+1
    $t104 := 0bv32;
    assume $IsValid'bv32'($t104);

    // $t105 := !=($t103, $t104) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:248:13+22
    $t105 := !$IsEqual'bv32'($t103, $t104);

    // if ($t105) goto L41 else goto L43 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:248:9+132
    if ($t105) { goto L41; } else { goto L43; }

    // label L41 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:249:45+5
    assume {:print "$at(13,9018,9023)"} true;
L41:

    // $t106 := 179736315981702064433883588727 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:249:52+34
    assume {:print "$at(13,9025,9059)"} true;
    $t106 := 179736315981702064433883588727;
    assume $IsValid'u128'($t106);

    // $t107 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:249:88+4
    $t107 := 96;
    assume $IsValid'u8'($t107);

    // $t108 := full_math_u128::mul_shr($t2, $t106, $t107) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:249:21+72
    call $t108 := $aa_full_math_u128_mul_shr($t2, $t106, $t107);
    if ($abort_flag) {
        assume {:print "$at(13,8994,9066)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t108 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:249:13+80
    $t2 := $t108;

    // trace_local[ratio]($t108) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:249:13+80
    assume {:print "$track_local(102,4,2):", $t108} $t108 == $t108;

    // label L43 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:251:13+8
    assume {:print "$at(13,9090,9098)"} true;
L43:

    // $t109 := 32768 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:251:24+6
    assume {:print "$at(13,9101,9107)"} true;
    $t109 := 32768;
    assume $IsValid'u32'($t109);

    // $t110 := &($t5, $t109) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:251:13+17
    call $t110 := $AndBv32($t5, $int2bv.32($t109));

    // $t111 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:251:34+1
    $t111 := 0bv32;
    assume $IsValid'bv32'($t111);

    // $t112 := !=($t110, $t111) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:251:13+22
    $t112 := !$IsEqual'bv32'($t110, $t111);

    // if ($t112) goto L44 else goto L46 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:251:9+132
    if ($t112) { goto L44; } else { goto L46; }

    // label L44 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:252:45+5
    assume {:print "$at(13,9160,9165)"} true;
L44:

    // $t113 := 407748233172238350107850275304 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:252:52+34
    assume {:print "$at(13,9167,9201)"} true;
    $t113 := 407748233172238350107850275304;
    assume $IsValid'u128'($t113);

    // $t114 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:252:88+4
    $t114 := 96;
    assume $IsValid'u8'($t114);

    // $t115 := full_math_u128::mul_shr($t2, $t113, $t114) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:252:21+72
    call $t115 := $aa_full_math_u128_mul_shr($t2, $t113, $t114);
    if ($abort_flag) {
        assume {:print "$at(13,9136,9208)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t115 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:252:13+80
    $t2 := $t115;

    // trace_local[ratio]($t115) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:252:13+80
    assume {:print "$track_local(102,4,2):", $t115} $t115 == $t115;

    // label L46 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:254:13+8
    assume {:print "$at(13,9232,9240)"} true;
L46:

    // $t116 := 65536 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:254:24+7
    assume {:print "$at(13,9243,9250)"} true;
    $t116 := 65536;
    assume $IsValid'u32'($t116);

    // $t117 := &($t5, $t116) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:254:13+18
    call $t117 := $AndBv32($t5, $int2bv.32($t116));

    // $t118 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:254:35+1
    $t118 := 0bv32;
    assume $IsValid'bv32'($t118);

    // $t119 := !=($t117, $t118) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:254:13+23
    $t119 := !$IsEqual'bv32'($t117, $t118);

    // if ($t119) goto L47 else goto L49 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:254:9+134
    if ($t119) { goto L47; } else { goto L49; }

    // label L47 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:255:45+5
    assume {:print "$at(13,9303,9308)"} true;
L47:

    // $t120 := 2098478828474011932436660412517 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:255:52+35
    assume {:print "$at(13,9310,9345)"} true;
    $t120 := 2098478828474011932436660412517;
    assume $IsValid'u128'($t120);

    // $t121 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:255:89+4
    $t121 := 96;
    assume $IsValid'u8'($t121);

    // $t122 := full_math_u128::mul_shr($t2, $t120, $t121) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:255:21+73
    call $t122 := $aa_full_math_u128_mul_shr($t2, $t120, $t121);
    if ($abort_flag) {
        assume {:print "$at(13,9279,9352)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t122 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:255:13+81
    $t2 := $t122;

    // trace_local[ratio]($t122) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:255:13+81
    assume {:print "$track_local(102,4,2):", $t122} $t122 == $t122;

    // label L49 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:257:13+8
    assume {:print "$at(13,9376,9384)"} true;
L49:

    // $t123 := 131072 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:257:24+7
    assume {:print "$at(13,9387,9394)"} true;
    $t123 := 131072;
    assume $IsValid'u32'($t123);

    // $t124 := &($t5, $t123) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:257:13+18
    call $t124 := $AndBv32($t5, $int2bv.32($t123));

    // $t125 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:257:35+1
    $t125 := 0bv32;
    assume $IsValid'bv32'($t125);

    // $t126 := !=($t124, $t125) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:257:13+23
    $t126 := !$IsEqual'bv32'($t124, $t125);

    // if ($t126) goto L50 else goto L52 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:257:9+135
    if ($t126) { goto L50; } else { goto L52; }

    // label L50 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:258:45+5
    assume {:print "$at(13,9447,9452)"} true;
L50:

    // $t127 := 55581415166113811149459800483533 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:258:52+36
    assume {:print "$at(13,9454,9490)"} true;
    $t127 := 55581415166113811149459800483533;
    assume $IsValid'u128'($t127);

    // $t128 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:258:90+4
    $t128 := 96;
    assume $IsValid'u8'($t128);

    // $t129 := full_math_u128::mul_shr($t2, $t127, $t128) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:258:21+74
    call $t129 := $aa_full_math_u128_mul_shr($t2, $t127, $t128);
    if ($abort_flag) {
        assume {:print "$at(13,9423,9497)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t129 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:258:13+82
    $t2 := $t129;

    // trace_local[ratio]($t129) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:258:13+82
    assume {:print "$track_local(102,4,2):", $t129} $t129 == $t129;

    // label L52 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:260:13+8
    assume {:print "$at(13,9521,9529)"} true;
L52:

    // $t130 := 262144 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:260:24+7
    assume {:print "$at(13,9532,9539)"} true;
    $t130 := 262144;
    assume $IsValid'u32'($t130);

    // $t131 := &($t5, $t130) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:260:13+18
    call $t131 := $AndBv32($t5, $int2bv.32($t130));

    // $t132 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:260:35+1
    $t132 := 0bv32;
    assume $IsValid'bv32'($t132);

    // $t133 := !=($t131, $t132) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:260:13+23
    $t133 := !$IsEqual'bv32'($t131, $t132);

    // if ($t133) goto L53 else goto L55 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:260:9+138
    if ($t133) { goto L53; } else { goto L55; }

    // label L53 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:261:45+5
    assume {:print "$at(13,9592,9597)"} true;
L53:

    // $t134 := 38992368544603139932233054999993551 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:261:52+39
    assume {:print "$at(13,9599,9638)"} true;
    $t134 := 38992368544603139932233054999993551;
    assume $IsValid'u128'($t134);

    // $t135 := 96 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:261:93+4
    $t135 := 96;
    assume $IsValid'u8'($t135);

    // $t136 := full_math_u128::mul_shr($t2, $t134, $t135) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:261:21+77
    call $t136 := $aa_full_math_u128_mul_shr($t2, $t134, $t135);
    if ($abort_flag) {
        assume {:print "$at(13,9568,9645)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // $t2 := $t136 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:261:13+85
    $t2 := $t136;

    // trace_local[ratio]($t136) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:261:13+85
    assume {:print "$track_local(102,4,2):", $t136} $t136 == $t136;

    // label L55 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:264:9+5
    assume {:print "$at(13,9666,9671)"} true;
L55:

    // $t137 := 32 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:264:18+2
    assume {:print "$at(13,9675,9677)"} true;
    $t137 := 32;
    assume $IsValid'u8'($t137);

    // $t138 := >>($t2, $t137) on_abort goto L58 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:264:9+11
    call $t138 := $ShrU128($t2, $t137);
    if ($abort_flag) {
        assume {:print "$at(13,9666,9677)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,4):", $t4} $t4 == $t4;
        goto L58;
    }

    // trace_return[0]($t138) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:201:63+2782
    assume {:print "$at(13,6901,9683)"} true;
    assume {:print "$track_return(102,4,0):", $t138} $t138 == $t138;

    // goto L57 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:201:63+2782
    goto L57;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:206:13+33
    assume {:print "$at(13,7077,7110)"} true;
L0:

    // $t139 := 79228162514264337593543950336 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:206:13+33
    assume {:print "$at(13,7077,7110)"} true;
    $t139 := 79228162514264337593543950336;
    assume $IsValid'u128'($t139);

    // $t2 := $t139 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:206:13+33
    $t2 := $t139;

    // trace_local[ratio]($t139) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:206:13+33
    assume {:print "$track_local(102,4,2):", $t139} $t139 == $t139;

    // goto L56 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:206:13+33
    goto L56;

    // label L57 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:265:5+1
    assume {:print "$at(13,9682,9683)"} true;
L57:

    // return $t138 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:265:5+1
    assume {:print "$at(13,9682,9683)"} true;
    $ret0 := $t138;
    return;

    // label L58 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:265:5+1
L58:

    // abort($t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:265:5+1
    assume {:print "$at(13,9682,9683)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun tick_math::get_sqrt_price_at_tick [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:56:5+313
procedure {:inline 1} $aa_tick_math_get_sqrt_price_at_tick(_$t0: $aa_i32_I32) returns ($ret0: int)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: $aa_i32_I32;
    var $t4: int;
    var $t5: bool;
    var $t6: $aa_i32_I32;
    var $t7: bool;
    var $t8: bool;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: bool;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'bool': bool;
    var $temp_0'u128': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[tick]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:56:5+1
    assume {:print "$at(13,1603,1604)"} true;
    assume {:print "$track_local(102,5,0):", $t0} $t0 == $t0;

    // $t3 := tick_math::min_tick() on_abort goto L9 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:32+10
    assume {:print "$at(13,1692,1702)"} true;
    call $t3 := $aa_tick_math_min_tick();
    if ($abort_flag) {
        assume {:print "$at(13,1692,1702)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,5):", $t4} $t4 == $t4;
        goto L9;
    }

    // $t5 := i32::gte($t0, $t3) on_abort goto L9 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:17+26
    call $t5 := $aa_i32_gte($t0, $t3);
    if ($abort_flag) {
        assume {:print "$at(13,1677,1703)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,5):", $t4} $t4 == $t4;
        goto L9;
    }

    // if ($t5) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:17+56
    if ($t5) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:56+4
L1:

    // $t6 := tick_math::max_tick() on_abort goto L9 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:62+10
    assume {:print "$at(13,1722,1732)"} true;
    call $t6 := $aa_tick_math_max_tick();
    if ($abort_flag) {
        assume {:print "$at(13,1722,1732)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,5):", $t4} $t4 == $t4;
        goto L9;
    }

    // $t7 := i32::lte($t0, $t6) on_abort goto L9 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:47+26
    call $t7 := $aa_i32_lte($t0, $t6);
    if ($abort_flag) {
        assume {:print "$at(13,1707,1733)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,5):", $t4} $t4 == $t4;
        goto L9;
    }

    // $t1 := $t7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:47+26
    $t1 := $t7;

    // trace_local[$t3]($t7) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:47+26
    assume {:print "$track_local(102,5,1):", $t7} $t7 == $t7;

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:9+6
L7:

    // if ($t1) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:9+6
    assume {:print "$at(13,1669,1675)"} true;
    if ($t1) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:58:13+17
    assume {:print "$at(13,1763,1780)"} true;
L3:

    // $t8 := i32::is_neg($t0) on_abort goto L9 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:58:13+17
    assume {:print "$at(13,1763,1780)"} true;
    call $t8 := $aa_i32_is_neg($t0);
    if ($abort_flag) {
        assume {:print "$at(13,1763,1780)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,5):", $t4} $t4 == $t4;
        goto L9;
    }

    // if ($t8) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:58:9+151
    if ($t8) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:59:13+37
    assume {:print "$at(13,1796,1833)"} true;
L5:

    // $t9 := tick_math::get_sqrt_price_at_negative_tick($t0) on_abort goto L9 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:59:13+37
    assume {:print "$at(13,1796,1833)"} true;
    call $t9 := $aa_tick_math_get_sqrt_price_at_negative_tick($t0);
    if ($abort_flag) {
        assume {:print "$at(13,1796,1833)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,5):", $t4} $t4 == $t4;
        goto L9;
    }

    // $t2 := $t9 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:59:13+37
    $t2 := $t9;

    // trace_local[return]($t9) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:59:13+37
    assume {:print "$track_local(102,5,2):", $t9} $t9 == $t9;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:56:61+257
    assume {:print "$at(13,1659,1916)"} true;
L6:

    // trace_return[0]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:56:61+257
    assume {:print "$at(13,1659,1916)"} true;
    assume {:print "$track_return(102,5,0):", $t2} $t2 == $t2;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:56:61+257
    goto L8;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:61:13+37
    assume {:print "$at(13,1863,1900)"} true;
L4:

    // $t10 := tick_math::get_sqrt_price_at_positive_tick($t0) on_abort goto L9 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:61:13+37
    assume {:print "$at(13,1863,1900)"} true;
    call $t10 := $aa_tick_math_get_sqrt_price_at_positive_tick($t0);
    if ($abort_flag) {
        assume {:print "$at(13,1863,1900)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(102,5):", $t4} $t4 == $t4;
        goto L9;
    }

    // $t2 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:61:13+37
    $t2 := $t10;

    // trace_local[return]($t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:61:13+37
    assume {:print "$track_local(102,5,2):", $t10} $t10 == $t10;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:61:13+37
    goto L6;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:75+13
    assume {:print "$at(13,1735,1748)"} true;
L2:

    // $t11 := 500004 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:75+13
    assume {:print "$at(13,1735,1748)"} true;
    $t11 := 500004;
    assume $IsValid'u64'($t11);

    // trace_abort($t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:9+6
    assume {:print "$at(13,1669,1675)"} true;
    assume {:print "$track_abort(102,5):", $t11} $t11 == $t11;

    // $t4 := move($t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:9+6
    $t4 := $t11;

    // goto L9 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:9+6
    goto L9;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:17+56
L0:

    // $t12 := false at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:17+56
    assume {:print "$at(13,1677,1733)"} true;
    $t12 := false;
    assume $IsValid'bool'($t12);

    // $t1 := $t12 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:17+56
    $t1 := $t12;

    // trace_local[$t3]($t12) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:17+56
    assume {:print "$track_local(102,5,1):", $t12} $t12 == $t12;

    // goto L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:57:17+56
    goto L7;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:63:5+1
    assume {:print "$at(13,1915,1916)"} true;
L8:

    // return $t2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:63:5+1
    assume {:print "$at(13,1915,1916)"} true;
    $ret0 := $t2;
    return;

    // label L9 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:63:5+1
L9:

    // abort($t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:63:5+1
    assume {:print "$at(13,1915,1916)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun tick_math::max_tick [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:29:5+69
procedure {:inline 1} $aa_tick_math_max_tick() returns ($ret0: $aa_i32_I32)
{
    // declare local variables
    var $t0: int;
    var $t1: $aa_i32_I32;
    var $t2: int;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;

    // bytecode translation starts here
    // $t0 := 443636 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:30:19+10
    assume {:print "$at(13,824,834)"} true;
    $t0 := 443636;
    assume $IsValid'u32'($t0);

    // $t1 := i32::from($t0) on_abort goto L2 with $t2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:30:9+21
    call $t1 := $aa_i32_from($t0);
    if ($abort_flag) {
        assume {:print "$at(13,814,835)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(102,10):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:30:9+21
    assume {:print "$track_return(102,10,0):", $t1} $t1 == $t1;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:31:5+1
    assume {:print "$at(13,840,841)"} true;
L1:

    // return $t1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:31:5+1
    assume {:print "$at(13,840,841)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:31:5+1
L2:

    // abort($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:31:5+1
    assume {:print "$at(13,840,841)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun tick_math::min_tick [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:33:5+73
procedure {:inline 1} $aa_tick_math_min_tick() returns ($ret0: $aa_i32_I32)
{
    // declare local variables
    var $t0: bv32;
    var $t1: $aa_i32_I32;
    var $t2: int;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;

    // bytecode translation starts here
    // $t0 := 443636 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:34:23+10
    assume {:print "$at(13,903,913)"} true;
    $t0 := 443636bv32;
    assume $IsValid'bv32'($t0);

    // $t1 := i32::neg_from($t0) on_abort goto L2 with $t2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:34:9+25
    call $t1 := $aa_i32_neg_from($t0);
    if ($abort_flag) {
        assume {:print "$at(13,889,914)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(102,12):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:34:9+25
    assume {:print "$track_return(102,12,0):", $t1} $t1 == $t1;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:35:5+1
    assume {:print "$at(13,919,920)"} true;
L1:

    // return $t1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:35:5+1
    assume {:print "$at(13,919,920)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:35:5+1
L2:

    // abort($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/tick_math.move:35:5+1
    assume {:print "$at(13,919,920)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// struct tick_bitmap::BitMap at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/tick_bitmap.move:10:5+61
datatype $aa_tick_bitmap_BitMap {
    $aa_tick_bitmap_BitMap($map: Table int (int))
}
function {:inline} $Update'$aa_tick_bitmap_BitMap'_map(s: $aa_tick_bitmap_BitMap, x: Table int (int)): $aa_tick_bitmap_BitMap {
    $aa_tick_bitmap_BitMap(x)
}
function $IsValid'$aa_tick_bitmap_BitMap'(s: $aa_tick_bitmap_BitMap): bool {
    $IsValid'$1_table_Table'$aa_i32_I32_u256''(s->$map)
}
function {:inline} $IsEqual'$aa_tick_bitmap_BitMap'(s1: $aa_tick_bitmap_BitMap, s2: $aa_tick_bitmap_BitMap): bool {
    s1 == s2
}

// fun liquidity_math::sub_delta [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/liquidity_math.move:9:5+78
procedure {:inline 1} $aa_liquidity_math_sub_delta(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u128': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[net]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/liquidity_math.move:9:5+1
    assume {:print "$at(9,178,179)"} true;
    assume {:print "$track_local(106,1,0):", $t0} $t0 == $t0;

    // trace_local[delta]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/liquidity_math.move:9:5+1
    assume {:print "$track_local(106,1,1):", $t1} $t1 == $t1;

    // $t2 := -($t0, $t1) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/liquidity_math.move:10:9+11
    assume {:print "$at(9,239,250)"} true;
    call $t2 := $Sub($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(9,239,250)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(106,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/liquidity_math.move:10:9+11
    assume {:print "$track_return(106,1,0):", $t2} $t2 == $t2;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/liquidity_math.move:11:5+1
    assume {:print "$at(9,255,256)"} true;
L1:

    // return $t2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/liquidity_math.move:11:5+1
    assume {:print "$at(9,255,256)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/liquidity_math.move:11:5+1
L2:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/liquidity_math.move:11:5+1
    assume {:print "$at(9,255,256)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct tick::TickInfo at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/tick.move:11:5+1513
datatype $aa_tick_TickInfo {
    $aa_tick_TickInfo($liquidity_gross: int, $liquidity_net: $aa_i128_I128, $fee_growth_outside_a: int, $fee_growth_outside_b: int, $tick_cumulative_outside: int, $seconds_per_liquidity_oracle_outside: int, $seconds_per_liquidity_incentive_outside: int, $emissions_per_liquidity_incentive_outside: Vec (int), $seconds_outside: int, $initialized: bool)
}
function {:inline} $Update'$aa_tick_TickInfo'_liquidity_gross(s: $aa_tick_TickInfo, x: int): $aa_tick_TickInfo {
    $aa_tick_TickInfo(x, s->$liquidity_net, s->$fee_growth_outside_a, s->$fee_growth_outside_b, s->$tick_cumulative_outside, s->$seconds_per_liquidity_oracle_outside, s->$seconds_per_liquidity_incentive_outside, s->$emissions_per_liquidity_incentive_outside, s->$seconds_outside, s->$initialized)
}
function {:inline} $Update'$aa_tick_TickInfo'_liquidity_net(s: $aa_tick_TickInfo, x: $aa_i128_I128): $aa_tick_TickInfo {
    $aa_tick_TickInfo(s->$liquidity_gross, x, s->$fee_growth_outside_a, s->$fee_growth_outside_b, s->$tick_cumulative_outside, s->$seconds_per_liquidity_oracle_outside, s->$seconds_per_liquidity_incentive_outside, s->$emissions_per_liquidity_incentive_outside, s->$seconds_outside, s->$initialized)
}
function {:inline} $Update'$aa_tick_TickInfo'_fee_growth_outside_a(s: $aa_tick_TickInfo, x: int): $aa_tick_TickInfo {
    $aa_tick_TickInfo(s->$liquidity_gross, s->$liquidity_net, x, s->$fee_growth_outside_b, s->$tick_cumulative_outside, s->$seconds_per_liquidity_oracle_outside, s->$seconds_per_liquidity_incentive_outside, s->$emissions_per_liquidity_incentive_outside, s->$seconds_outside, s->$initialized)
}
function {:inline} $Update'$aa_tick_TickInfo'_fee_growth_outside_b(s: $aa_tick_TickInfo, x: int): $aa_tick_TickInfo {
    $aa_tick_TickInfo(s->$liquidity_gross, s->$liquidity_net, s->$fee_growth_outside_a, x, s->$tick_cumulative_outside, s->$seconds_per_liquidity_oracle_outside, s->$seconds_per_liquidity_incentive_outside, s->$emissions_per_liquidity_incentive_outside, s->$seconds_outside, s->$initialized)
}
function {:inline} $Update'$aa_tick_TickInfo'_tick_cumulative_outside(s: $aa_tick_TickInfo, x: int): $aa_tick_TickInfo {
    $aa_tick_TickInfo(s->$liquidity_gross, s->$liquidity_net, s->$fee_growth_outside_a, s->$fee_growth_outside_b, x, s->$seconds_per_liquidity_oracle_outside, s->$seconds_per_liquidity_incentive_outside, s->$emissions_per_liquidity_incentive_outside, s->$seconds_outside, s->$initialized)
}
function {:inline} $Update'$aa_tick_TickInfo'_seconds_per_liquidity_oracle_outside(s: $aa_tick_TickInfo, x: int): $aa_tick_TickInfo {
    $aa_tick_TickInfo(s->$liquidity_gross, s->$liquidity_net, s->$fee_growth_outside_a, s->$fee_growth_outside_b, s->$tick_cumulative_outside, x, s->$seconds_per_liquidity_incentive_outside, s->$emissions_per_liquidity_incentive_outside, s->$seconds_outside, s->$initialized)
}
function {:inline} $Update'$aa_tick_TickInfo'_seconds_per_liquidity_incentive_outside(s: $aa_tick_TickInfo, x: int): $aa_tick_TickInfo {
    $aa_tick_TickInfo(s->$liquidity_gross, s->$liquidity_net, s->$fee_growth_outside_a, s->$fee_growth_outside_b, s->$tick_cumulative_outside, s->$seconds_per_liquidity_oracle_outside, x, s->$emissions_per_liquidity_incentive_outside, s->$seconds_outside, s->$initialized)
}
function {:inline} $Update'$aa_tick_TickInfo'_emissions_per_liquidity_incentive_outside(s: $aa_tick_TickInfo, x: Vec (int)): $aa_tick_TickInfo {
    $aa_tick_TickInfo(s->$liquidity_gross, s->$liquidity_net, s->$fee_growth_outside_a, s->$fee_growth_outside_b, s->$tick_cumulative_outside, s->$seconds_per_liquidity_oracle_outside, s->$seconds_per_liquidity_incentive_outside, x, s->$seconds_outside, s->$initialized)
}
function {:inline} $Update'$aa_tick_TickInfo'_seconds_outside(s: $aa_tick_TickInfo, x: int): $aa_tick_TickInfo {
    $aa_tick_TickInfo(s->$liquidity_gross, s->$liquidity_net, s->$fee_growth_outside_a, s->$fee_growth_outside_b, s->$tick_cumulative_outside, s->$seconds_per_liquidity_oracle_outside, s->$seconds_per_liquidity_incentive_outside, s->$emissions_per_liquidity_incentive_outside, x, s->$initialized)
}
function {:inline} $Update'$aa_tick_TickInfo'_initialized(s: $aa_tick_TickInfo, x: bool): $aa_tick_TickInfo {
    $aa_tick_TickInfo(s->$liquidity_gross, s->$liquidity_net, s->$fee_growth_outside_a, s->$fee_growth_outside_b, s->$tick_cumulative_outside, s->$seconds_per_liquidity_oracle_outside, s->$seconds_per_liquidity_incentive_outside, s->$emissions_per_liquidity_incentive_outside, s->$seconds_outside, x)
}
function $IsValid'$aa_tick_TickInfo'(s: $aa_tick_TickInfo): bool {
    $IsValid'u128'(s->$liquidity_gross)
      && $IsValid'$aa_i128_I128'(s->$liquidity_net)
      && $IsValid'u128'(s->$fee_growth_outside_a)
      && $IsValid'u128'(s->$fee_growth_outside_b)
      && $IsValid'u64'(s->$tick_cumulative_outside)
      && $IsValid'u128'(s->$seconds_per_liquidity_oracle_outside)
      && $IsValid'u128'(s->$seconds_per_liquidity_incentive_outside)
      && $IsValid'vec'u128''(s->$emissions_per_liquidity_incentive_outside)
      && $IsValid'u64'(s->$seconds_outside)
      && $IsValid'bool'(s->$initialized)
}
function {:inline} $IsEqual'$aa_tick_TickInfo'(s1: $aa_tick_TickInfo, s2: $aa_tick_TickInfo): bool {
    $IsEqual'u128'(s1->$liquidity_gross, s2->$liquidity_gross)
    && $IsEqual'$aa_i128_I128'(s1->$liquidity_net, s2->$liquidity_net)
    && $IsEqual'u128'(s1->$fee_growth_outside_a, s2->$fee_growth_outside_a)
    && $IsEqual'u128'(s1->$fee_growth_outside_b, s2->$fee_growth_outside_b)
    && $IsEqual'u64'(s1->$tick_cumulative_outside, s2->$tick_cumulative_outside)
    && $IsEqual'u128'(s1->$seconds_per_liquidity_oracle_outside, s2->$seconds_per_liquidity_oracle_outside)
    && $IsEqual'u128'(s1->$seconds_per_liquidity_incentive_outside, s2->$seconds_per_liquidity_incentive_outside)
    && $IsEqual'vec'u128''(s1->$emissions_per_liquidity_incentive_outside, s2->$emissions_per_liquidity_incentive_outside)
    && $IsEqual'u64'(s1->$seconds_outside, s2->$seconds_outside)
    && $IsEqual'bool'(s1->$initialized, s2->$initialized)}

// fun math_u256::checked_shlw [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:18:5+204
procedure {:inline 1} $aa_math_u256_checked_shlw(_$t0: int) returns ($ret0: int, $ret1: bool)
{
    // declare local variables
    var $t1: int;
    var $t2: bool;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: bool;
    var $t0: int;
    var $temp_0'bool': bool;
    var $temp_0'u256': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[n]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:18:5+1
    assume {:print "$at(11,408,409)"} true;
    assume {:print "$track_local(108,1,0):", $t0} $t0 == $t0;

    // $t3 := 115792089237316195417293883273301227089434195242432897623355228563449095127040 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:20:17+4
    assume {:print "$at(11,519,523)"} true;
    $t3 := 115792089237316195417293883273301227089434195242432897623355228563449095127040;
    assume $IsValid'u256'($t3);

    // $t4 := >($t0, $t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:20:13+8
    call $t4 := $Gt($t0, $t3);

    // if ($t4) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:20:9+95
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:21:14+1
    assume {:print "$at(11,540,541)"} true;
L1:

    // $t5 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:21:14+1
    assume {:print "$at(11,540,541)"} true;
    $t5 := 0;
    assume $IsValid'u256'($t5);

    // $t1 := $t5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:21:14+1
    $t1 := $t5;

    // trace_local[$t4]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:21:14+1
    assume {:print "$track_local(108,1,1):", $t5} $t5 == $t5;

    // $t6 := true at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:21:17+4
    $t6 := true;
    assume $IsValid'bool'($t6);

    // $t2 := $t6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:21:17+4
    $t2 := $t6;

    // trace_local[$t3]($t6) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:21:17+4
    assume {:print "$track_local(108,1,2):", $t6} $t6 == $t6;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:20:9+95
    assume {:print "$at(11,511,606)"} true;
L2:

    // trace_return[0]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:20:9+95
    assume {:print "$at(11,511,606)"} true;
    assume {:print "$track_return(108,1,0):", $t1} $t1 == $t1;

    // trace_return[1]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:20:9+95
    assume {:print "$track_return(108,1,1):", $t2} $t2 == $t2;

    // goto L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:20:9+95
    goto L3;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:23:15+1
    assume {:print "$at(11,580,581)"} true;
L0:

    // $t7 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:23:20+2
    assume {:print "$at(11,585,587)"} true;
    $t7 := 64;
    assume $IsValid'u8'($t7);

    // $t8 := <<($t0, $t7) on_abort goto L4 with $t9 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:23:14+9
    call $t8 := $ShlU256($t0, $t7);
    if ($abort_flag) {
        assume {:print "$at(11,579,588)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(108,1):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t1 := $t8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:23:14+9
    $t1 := $t8;

    // trace_local[$t4]($t8) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:23:14+9
    assume {:print "$track_local(108,1,1):", $t8} $t8 == $t8;

    // $t10 := false at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:23:25+5
    $t10 := false;
    assume $IsValid'bool'($t10);

    // $t2 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:23:25+5
    $t2 := $t10;

    // trace_local[$t3]($t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:23:25+5
    assume {:print "$track_local(108,1,2):", $t10} $t10 == $t10;

    // goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:23:25+5
    goto L2;

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:25:5+1
    assume {:print "$at(11,611,612)"} true;
L3:

    // return ($t1, $t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:25:5+1
    assume {:print "$at(11,611,612)"} true;
    $ret0 := $t1;
    $ret1 := $t2;
    return;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:25:5+1
L4:

    // abort($t9) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:25:5+1
    assume {:print "$at(11,611,612)"} true;
    $abort_code := $t9;
    $abort_flag := true;
    return;

}

// fun math_u256::div_round [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:27:5+210
procedure {:inline 1} $aa_math_u256_div_round(_$t0: int, _$t1: int, _$t2: bool) returns ($ret0: int)
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t9: int;
    var $t10: int;
    var $t11: bool;
    var $t0: int;
    var $t1: int;
    var $t2: bool;
    var $temp_0'bool': bool;
    var $temp_0'u256': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[num]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:27:5+1
    assume {:print "$at(11,618,619)"} true;
    assume {:print "$track_local(108,3,0):", $t0} $t0 == $t0;

    // trace_local[denom]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:27:5+1
    assume {:print "$track_local(108,3,1):", $t1} $t1 == $t1;

    // trace_local[round_up]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:27:5+1
    assume {:print "$track_local(108,3,2):", $t2} $t2 == $t2;

    // $t5 := /($t0, $t1) on_abort goto L7 with $t6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:28:17+11
    assume {:print "$at(11,703,714)"} true;
    call $t5 := $Div($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(11,703,714)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(108,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_local[$t5]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:28:17+11
    assume {:print "$track_local(108,3,3):", $t5} $t5 == $t5;

    // if ($t2) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:13+32
    assume {:print "$at(11,728,760)"} true;
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:27+1
L1:

    // $t7 := *($t5, $t1) on_abort goto L7 with $t6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:26+11
    assume {:print "$at(11,741,752)"} true;
    call $t7 := $MulU256($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(11,741,752)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(108,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t8 := !=($t7, $t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:25+20
    $t8 := !$IsEqual'u256'($t7, $t0);

    // $t2 := $t8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:25+20
    $t2 := $t8;

    // trace_local[round_up]($t8) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:25+20
    assume {:print "$track_local(108,3,2):", $t8} $t8 == $t8;

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:9+98
L5:

    // if ($t2) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:9+98
    assume {:print "$at(11,724,822)"} true;
    if ($t2) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:30:13+1
    assume {:print "$at(11,776,777)"} true;
L3:

    // $t9 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:30:17+1
    assume {:print "$at(11,780,781)"} true;
    $t9 := 1;
    assume $IsValid'u256'($t9);

    // $t10 := +($t5, $t9) on_abort goto L7 with $t6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:30:13+5
    call $t10 := $AddU256($t5, $t9);
    if ($abort_flag) {
        assume {:print "$at(11,776,781)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(108,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t4 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:30:13+5
    $t4 := $t10;

    // trace_local[$t8]($t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:30:13+5
    assume {:print "$track_local(108,3,4):", $t10} $t10 == $t10;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:9+98
    assume {:print "$at(11,724,822)"} true;
L4:

    // trace_return[0]($t4) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:9+98
    assume {:print "$at(11,724,822)"} true;
    assume {:print "$track_return(108,3,0):", $t4} $t4 == $t4;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:9+98
    goto L6;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:32:13+1
    assume {:print "$at(11,811,812)"} true;
L2:

    // $t4 := $t5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:32:13+1
    assume {:print "$at(11,811,812)"} true;
    $t4 := $t5;

    // trace_local[$t8]($t5) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:32:13+1
    assume {:print "$track_local(108,3,4):", $t5} $t5 == $t5;

    // goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:32:13+1
    goto L4;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:13+32
    assume {:print "$at(11,728,760)"} true;
L0:

    // $t11 := false at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:13+32
    assume {:print "$at(11,728,760)"} true;
    $t11 := false;
    assume $IsValid'bool'($t11);

    // $t2 := $t11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:13+32
    $t2 := $t11;

    // trace_local[round_up]($t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:13+32
    assume {:print "$track_local(108,3,2):", $t11} $t11 == $t11;

    // goto L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:29:13+32
    goto L5;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:34:5+1
    assume {:print "$at(11,827,828)"} true;
L6:

    // return $t4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:34:5+1
    assume {:print "$at(11,827,828)"} true;
    $ret0 := $t4;
    return;

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:34:5+1
L7:

    // abort($t6) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/math_u256.move:34:5+1
    assume {:print "$at(11,827,828)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun swap_math::get_delta_a [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:56:5+813
procedure {:inline 1} $aa_swap_math_get_delta_a(_$t0: int, _$t1: int, _$t2: int, _$t3: bool) returns ($ret0: int)
{
    // declare local variables
    var $t4: int;
    var $t5: bool;
    var $t6: bool;
    var $t7: int;
    var $t8: int;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: bool;
    var $t14: bool;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: bool;
    var $t20: int;
    var $t21: int;
    var $t22: int;
    var $t23: int;
    var $t24: int;
    var $t25: bool;
    var $t26: int;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: bool;
    var $temp_0'bool': bool;
    var $temp_0'u128': int;
    var $temp_0'u256': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // bytecode translation starts here
    // trace_local[sqrt_price_0]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:56:5+1
    assume {:print "$at(12,1691,1692)"} true;
    assume {:print "$track_local(110,3,0):", $t0} $t0 == $t0;

    // trace_local[sqrt_price_1]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:56:5+1
    assume {:print "$track_local(110,3,1):", $t1} $t1 == $t1;

    // trace_local[liquidity]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:56:5+1
    assume {:print "$track_local(110,3,2):", $t2} $t2 == $t2;

    // trace_local[round_up]($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:56:5+1
    assume {:print "$track_local(110,3,3):", $t3} $t3 == $t3;

    // $t9 := >($t0, $t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:62:35+27
    assume {:print "$at(12,1866,1893)"} true;
    call $t9 := $Gt($t0, $t1);

    // if ($t9) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:62:31+141
    if ($t9) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:63:13+12
    assume {:print "$at(12,1909,1921)"} true;
L1:

    // $t10 := -($t0, $t1) on_abort goto L11 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:63:13+27
    assume {:print "$at(12,1909,1936)"} true;
    call $t10 := $Sub($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(12,1909,1936)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,3):", $t11} $t11 == $t11;
        goto L11;
    }

    // $t4 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:63:13+27
    $t4 := $t10;

    // trace_local[$t7]($t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:63:13+27
    assume {:print "$track_local(110,3,4):", $t10} $t10 == $t10;

    // label L9 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:13+15
    assume {:print "$at(12,2017,2032)"} true;
L9:

    // $t12 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:32+1
    assume {:print "$at(12,2036,2037)"} true;
    $t12 := 0;
    assume $IsValid'u128'($t12);

    // $t13 := ==($t4, $t12) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:13+20
    $t13 := $IsEqual'u128'($t4, $t12);

    // if ($t13) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:13+38
    if ($t13) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:13+38
L3:

    // $t14 := true at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:13+38
    assume {:print "$at(12,2017,2055)"} true;
    $t14 := true;
    assume $IsValid'bool'($t14);

    // $t5 := $t14 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:13+38
    $t5 := $t14;

    // trace_local[$t6]($t14) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:13+38
    assume {:print "$track_local(110,3,5):", $t14} $t14 == $t14;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:9+76
L8:

    // if ($t5) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:9+76
    assume {:print "$at(12,2013,2089)"} true;
    if ($t5) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:68:20+1
    assume {:print "$at(12,2078,2079)"} true;
L5:

    // $t15 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:68:20+1
    assume {:print "$at(12,2078,2079)"} true;
    $t15 := 0;
    assume $IsValid'u64'($t15);

    // trace_return[0]($t15) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:68:13+8
    assume {:print "$track_return(110,3,0):", $t15} $t15 == $t15;

    // $t16 := move($t15) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:68:13+8
    $t16 := $t15;

    // goto L10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:68:13+8
    goto L10;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:71:38+9
    assume {:print "$at(12,2193,2202)"} true;
L4:

    // $t17 := full_math_u128::full_mul($t2, $t4) on_abort goto L11 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:71:13+52
    assume {:print "$at(12,2168,2220)"} true;
    call $t17 := $aa_full_math_u128_full_mul($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(12,2168,2220)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,3):", $t11} $t11 == $t11;
        goto L11;
    }

    // ($t18, $t19) := math_u256::checked_shlw($t17) on_abort goto L11 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:70:41+99
    assume {:print "$at(12,2131,2230)"} true;
    call $t18,$t19 := $aa_math_u256_checked_shlw($t17);
    if ($abort_flag) {
        assume {:print "$at(12,2131,2230)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,3):", $t11} $t11 == $t11;
        goto L11;
    }

    // trace_local[overflowing]($t19) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:73:9+71
    assume {:print "$at(12,2240,2311)"} true;
    assume {:print "$track_local(110,3,6):", $t19} $t19 == $t19;

    // trace_local[$t18]($t18) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:73:9+71
    assume {:print "$track_local(110,3,7):", $t18} $t18 == $t18;

    // if ($t19) goto L7 else goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:73:9+71
    if ($t19) { goto L7; } else { goto L6; }

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:74:19+24
    assume {:print "$at(12,2277,2301)"} true;
L7:

    // $t20 := 2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:74:19+24
    assume {:print "$at(12,2277,2301)"} true;
    $t20 := 2;
    assume $IsValid'u64'($t20);

    // trace_abort($t20) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:74:13+30
    assume {:print "$at(12,2271,2301)"} true;
    assume {:print "$track_abort(110,3):", $t20} $t20 == $t20;

    // $t11 := move($t20) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:74:13+30
    $t11 := $t20;

    // goto L11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:74:13+30
    goto L11;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:76:52+12
    assume {:print "$at(12,2364,2376)"} true;
L6:

    // $t21 := full_math_u128::full_mul($t0, $t1) on_abort goto L11 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:76:27+52
    assume {:print "$at(12,2339,2391)"} true;
    call $t21 := $aa_full_math_u128_full_mul($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(12,2339,2391)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,3):", $t11} $t11 == $t11;
        goto L11;
    }

    // trace_local[denominator]($t21) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:77:24+55
    assume {:print "$at(12,2416,2471)"} true;
    assume {:print "$track_local(110,3,8):", $t21} $t21 == $t21;

    // $t22 := math_u256::div_round($t18, $t21, $t3) on_abort goto L11 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:77:24+55
    call $t22 := $aa_math_u256_div_round($t18, $t21, $t3);
    if ($abort_flag) {
        assume {:print "$at(12,2416,2471)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,3):", $t11} $t11 == $t11;
        goto L11;
    }

    // $t23 := (u64)($t22) on_abort goto L11 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:78:9+17
    assume {:print "$at(12,2481,2498)"} true;
    call $t23 := $CastU64($t22);
    if ($abort_flag) {
        assume {:print "$at(12,2481,2498)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,3):", $t11} $t11 == $t11;
        goto L11;
    }

    // trace_return[0]($t23) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:61:12+674
    assume {:print "$at(12,1830,2504)"} true;
    assume {:print "$track_return(110,3,0):", $t23} $t23 == $t23;

    // $t16 := move($t23) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:61:12+674
    $t16 := $t23;

    // goto L10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:61:12+674
    goto L10;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:37+9
    assume {:print "$at(12,2041,2050)"} true;
L2:

    // $t24 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:50+1
    assume {:print "$at(12,2054,2055)"} true;
    $t24 := 0;
    assume $IsValid'u128'($t24);

    // $t25 := ==($t2, $t24) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:37+14
    $t25 := $IsEqual'u128'($t2, $t24);

    // $t5 := $t25 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:37+14
    $t5 := $t25;

    // trace_local[$t6]($t25) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:37+14
    assume {:print "$track_local(110,3,5):", $t25} $t25 == $t25;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:67:37+14
    goto L8;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:65:13+12
    assume {:print "$at(12,1966,1978)"} true;
L0:

    // $t26 := -($t1, $t0) on_abort goto L11 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:65:13+27
    assume {:print "$at(12,1966,1993)"} true;
    call $t26 := $Sub($t1, $t0);
    if ($abort_flag) {
        assume {:print "$at(12,1966,1993)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,3):", $t11} $t11 == $t11;
        goto L11;
    }

    // $t4 := $t26 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:65:13+27
    $t4 := $t26;

    // trace_local[$t7]($t26) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:65:13+27
    assume {:print "$track_local(110,3,4):", $t26} $t26 == $t26;

    // goto L9 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:65:13+27
    goto L9;

    // label L10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:79:5+1
    assume {:print "$at(12,2503,2504)"} true;
L10:

    // return $t16 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:79:5+1
    assume {:print "$at(12,2503,2504)"} true;
    $ret0 := $t16;
    return;

    // label L11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:79:5+1
L11:

    // abort($t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:79:5+1
    assume {:print "$at(12,2503,2504)"} true;
    $abort_code := $t11;
    $abort_flag := true;
    return;

}

// fun swap_math::get_delta_b [baseline] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:81:5+772
procedure {:inline 1} $aa_swap_math_get_delta_b(_$t0: int, _$t1: int, _$t2: int, _$t3: bool) returns ($ret0: int)
{
    // declare local variables
    var $t4: int;
    var $t5: bool;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: bool;
    var $t13: bool;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: bv256;
    var $t19: bv256;
    var $t20: bool;
    var $t21: int;
    var $t22: int;
    var $t23: int;
    var $t24: int;
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t28: int;
    var $t29: bool;
    var $t30: int;
    var $t31: bool;
    var $t32: int;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: bool;
    var $temp_0'bool': bool;
    var $temp_0'u128': int;
    var $temp_0'u256': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // bytecode translation starts here
    // trace_local[sqrt_price_0]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:81:5+1
    assume {:print "$at(12,2510,2511)"} true;
    assume {:print "$track_local(110,4,0):", $t0} $t0 == $t0;

    // trace_local[sqrt_price_1]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:81:5+1
    assume {:print "$track_local(110,4,1):", $t1} $t1 == $t1;

    // trace_local[liquidity]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:81:5+1
    assume {:print "$track_local(110,4,2):", $t2} $t2 == $t2;

    // trace_local[round_up]($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:81:5+1
    assume {:print "$track_local(110,4,3):", $t3} $t3 == $t3;

    // $t8 := >($t0, $t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:87:35+27
    assume {:print "$at(12,2685,2712)"} true;
    call $t8 := $Gt($t0, $t1);

    // if ($t8) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:87:31+141
    if ($t8) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:88:13+12
    assume {:print "$at(12,2728,2740)"} true;
L1:

    // $t9 := -($t0, $t1) on_abort goto L14 with $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:88:13+27
    assume {:print "$at(12,2728,2755)"} true;
    call $t9 := $Sub($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(12,2728,2755)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(110,4):", $t10} $t10 == $t10;
        goto L14;
    }

    // $t4 := $t9 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:88:13+27
    $t4 := $t9;

    // trace_local[$t7]($t9) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:88:13+27
    assume {:print "$track_local(110,4,4):", $t9} $t9 == $t9;

    // label L12 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:13+15
    assume {:print "$at(12,2836,2851)"} true;
L12:

    // $t11 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:32+1
    assume {:print "$at(12,2855,2856)"} true;
    $t11 := 0;
    assume $IsValid'u128'($t11);

    // $t12 := ==($t4, $t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:13+20
    $t12 := $IsEqual'u128'($t4, $t11);

    // if ($t12) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:13+38
    if ($t12) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:13+38
L3:

    // $t13 := true at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:13+38
    assume {:print "$at(12,2836,2874)"} true;
    $t13 := true;
    assume $IsValid'bool'($t13);

    // $t5 := $t13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:13+38
    $t5 := $t13;

    // trace_local[$t6]($t13) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:13+38
    assume {:print "$track_local(110,4,5):", $t13} $t13 == $t13;

    // label L11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:9+76
L11:

    // if ($t5) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:9+76
    assume {:print "$at(12,2832,2908)"} true;
    if ($t5) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:93:20+1
    assume {:print "$at(12,2897,2898)"} true;
L5:

    // $t14 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:93:20+1
    assume {:print "$at(12,2897,2898)"} true;
    $t14 := 0;
    assume $IsValid'u64'($t14);

    // trace_return[0]($t14) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:93:13+8
    assume {:print "$track_return(110,4,0):", $t14} $t14 == $t14;

    // $t15 := move($t14) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:93:13+8
    $t15 := $t14;

    // goto L13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:93:13+8
    goto L13;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:97:48+9
    assume {:print "$at(12,3050,3059)"} true;
L4:

    // $t16 := full_math_u128::full_mul($t2, $t4) on_abort goto L14 with $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:97:23+52
    assume {:print "$at(12,3025,3077)"} true;
    call $t16 := $aa_full_math_u128_full_mul($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(12,3025,3077)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(110,4):", $t10} $t10 == $t10;
        goto L14;
    }

    // trace_local[product]($t16) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:97:23+52
    assume {:print "$track_local(110,4,6):", $t16} $t16 == $t16;

    // if ($t3) goto L7 else goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:31+41
    assume {:print "$at(12,3109,3150)"} true;
    if ($t3) { goto L7; } else { goto L6; }

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:47+7
L7:

    // $t17 := 18446744073709551615 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:57+9
    assume {:print "$at(12,3135,3144)"} true;
    $t17 := 18446744073709551615;
    assume $IsValid'u256'($t17);

    // $t18 := &($t16, $t17) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:46+21
    call $t18 := $AndBv256($int2bv.256($t16), $int2bv.256($t17));

    // $t19 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:70+1
    $t19 := 0bv256;
    assume $IsValid'bv256'($t19);

    // $t20 := >($t18, $t19) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:45+27
    call $t20 := $GtBv256($t18, $t19);

    // $t7 := $t20 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:45+27
    $t7 := $t20;

    // trace_local[should_round_up]($t20) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:45+27
    assume {:print "$track_local(110,4,7):", $t20} $t20 == $t20;

    // label L10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:99:9+82
    assume {:print "$at(12,3160,3242)"} true;
L10:

    // if ($t7) goto L9 else goto L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:99:9+82
    assume {:print "$at(12,3160,3242)"} true;
    if ($t7) { goto L9; } else { goto L8; }

    // label L9 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:100:23+7
    assume {:print "$at(12,3205,3212)"} true;
L9:

    // $t21 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:100:34+2
    assume {:print "$at(12,3216,3218)"} true;
    $t21 := 64;
    assume $IsValid'u8'($t21);

    // $t22 := >>($t16, $t21) on_abort goto L14 with $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:100:22+15
    call $t22 := $ShrU256($t16, $t21);
    if ($abort_flag) {
        assume {:print "$at(12,3204,3219)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(110,4):", $t10} $t10 == $t10;
        goto L14;
    }

    // $t23 := 1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:100:40+1
    $t23 := 1;
    assume $IsValid'u256'($t23);

    // $t24 := +($t22, $t23) on_abort goto L14 with $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:100:21+21
    call $t24 := $AddU256($t22, $t23);
    if ($abort_flag) {
        assume {:print "$at(12,3203,3224)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(110,4):", $t10} $t10 == $t10;
        goto L14;
    }

    // $t25 := (u64)($t24) on_abort goto L14 with $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:100:20+30
    call $t25 := $CastU64($t24);
    if ($abort_flag) {
        assume {:print "$at(12,3202,3232)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(110,4):", $t10} $t10 == $t10;
        goto L14;
    }

    // trace_return[0]($t25) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:100:13+37
    assume {:print "$track_return(110,4,0):", $t25} $t25 == $t25;

    // $t15 := move($t25) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:100:13+37
    $t15 := $t25;

    // goto L13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:100:13+37
    goto L13;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:102:11+7
    assume {:print "$at(12,3254,3261)"} true;
L8:

    // $t26 := 64 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:102:22+2
    assume {:print "$at(12,3265,3267)"} true;
    $t26 := 64;
    assume $IsValid'u8'($t26);

    // $t27 := >>($t16, $t26) on_abort goto L14 with $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:102:10+15
    call $t27 := $ShrU256($t16, $t26);
    if ($abort_flag) {
        assume {:print "$at(12,3253,3268)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(110,4):", $t10} $t10 == $t10;
        goto L14;
    }

    // $t28 := (u64)($t27) on_abort goto L14 with $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:102:9+24
    call $t28 := $CastU64($t27);
    if ($abort_flag) {
        assume {:print "$at(12,3252,3276)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(110,4):", $t10} $t10 == $t10;
        goto L14;
    }

    // trace_return[0]($t28) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:86:12+633
    assume {:print "$at(12,2649,3282)"} true;
    assume {:print "$track_return(110,4,0):", $t28} $t28 == $t28;

    // $t15 := move($t28) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:86:12+633
    $t15 := $t28;

    // goto L13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:86:12+633
    goto L13;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:31+41
    assume {:print "$at(12,3109,3150)"} true;
L6:

    // $t29 := false at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:31+41
    assume {:print "$at(12,3109,3150)"} true;
    $t29 := false;
    assume $IsValid'bool'($t29);

    // $t7 := $t29 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:31+41
    $t7 := $t29;

    // trace_local[should_round_up]($t29) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:31+41
    assume {:print "$track_local(110,4,7):", $t29} $t29 == $t29;

    // goto L10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:98:31+41
    goto L10;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:37+9
    assume {:print "$at(12,2860,2869)"} true;
L2:

    // $t30 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:50+1
    assume {:print "$at(12,2873,2874)"} true;
    $t30 := 0;
    assume $IsValid'u128'($t30);

    // $t31 := ==($t2, $t30) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:37+14
    $t31 := $IsEqual'u128'($t2, $t30);

    // $t5 := $t31 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:37+14
    $t5 := $t31;

    // trace_local[$t6]($t31) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:37+14
    assume {:print "$track_local(110,4,5):", $t31} $t31 == $t31;

    // goto L11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:92:37+14
    goto L11;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:90:13+12
    assume {:print "$at(12,2785,2797)"} true;
L0:

    // $t32 := -($t1, $t0) on_abort goto L14 with $t10 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:90:13+27
    assume {:print "$at(12,2785,2812)"} true;
    call $t32 := $Sub($t1, $t0);
    if ($abort_flag) {
        assume {:print "$at(12,2785,2812)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(110,4):", $t10} $t10 == $t10;
        goto L14;
    }

    // $t4 := $t32 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:90:13+27
    $t4 := $t32;

    // trace_local[$t7]($t32) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:90:13+27
    assume {:print "$track_local(110,4,4):", $t32} $t32 == $t32;

    // goto L12 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:90:13+27
    goto L12;

    // label L13 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:103:5+1
    assume {:print "$at(12,3281,3282)"} true;
L13:

    // return $t15 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:103:5+1
    assume {:print "$at(12,3281,3282)"} true;
    $ret0 := $t15;
    return;

    // label L14 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:103:5+1
L14:

    // abort($t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/math/swap_math.move:103:5+1
    assume {:print "$at(12,3281,3282)"} true;
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// struct rewarder::Rewarder at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/rewarder.move:27:5+299
datatype $aa_rewarder_Rewarder {
    $aa_rewarder_Rewarder($reward_store: $1_object_Object'$1_fungible_asset_FungibleStore', $emissions_per_second: int, $emissions_per_second_max: int, $emissions_per_liquidity_start: int, $emissions_per_liquidity_latest: int, $user_owed: int, $pause: bool)
}
function {:inline} $Update'$aa_rewarder_Rewarder'_reward_store(s: $aa_rewarder_Rewarder, x: $1_object_Object'$1_fungible_asset_FungibleStore'): $aa_rewarder_Rewarder {
    $aa_rewarder_Rewarder(x, s->$emissions_per_second, s->$emissions_per_second_max, s->$emissions_per_liquidity_start, s->$emissions_per_liquidity_latest, s->$user_owed, s->$pause)
}
function {:inline} $Update'$aa_rewarder_Rewarder'_emissions_per_second(s: $aa_rewarder_Rewarder, x: int): $aa_rewarder_Rewarder {
    $aa_rewarder_Rewarder(s->$reward_store, x, s->$emissions_per_second_max, s->$emissions_per_liquidity_start, s->$emissions_per_liquidity_latest, s->$user_owed, s->$pause)
}
function {:inline} $Update'$aa_rewarder_Rewarder'_emissions_per_second_max(s: $aa_rewarder_Rewarder, x: int): $aa_rewarder_Rewarder {
    $aa_rewarder_Rewarder(s->$reward_store, s->$emissions_per_second, x, s->$emissions_per_liquidity_start, s->$emissions_per_liquidity_latest, s->$user_owed, s->$pause)
}
function {:inline} $Update'$aa_rewarder_Rewarder'_emissions_per_liquidity_start(s: $aa_rewarder_Rewarder, x: int): $aa_rewarder_Rewarder {
    $aa_rewarder_Rewarder(s->$reward_store, s->$emissions_per_second, s->$emissions_per_second_max, x, s->$emissions_per_liquidity_latest, s->$user_owed, s->$pause)
}
function {:inline} $Update'$aa_rewarder_Rewarder'_emissions_per_liquidity_latest(s: $aa_rewarder_Rewarder, x: int): $aa_rewarder_Rewarder {
    $aa_rewarder_Rewarder(s->$reward_store, s->$emissions_per_second, s->$emissions_per_second_max, s->$emissions_per_liquidity_start, x, s->$user_owed, s->$pause)
}
function {:inline} $Update'$aa_rewarder_Rewarder'_user_owed(s: $aa_rewarder_Rewarder, x: int): $aa_rewarder_Rewarder {
    $aa_rewarder_Rewarder(s->$reward_store, s->$emissions_per_second, s->$emissions_per_second_max, s->$emissions_per_liquidity_start, s->$emissions_per_liquidity_latest, x, s->$pause)
}
function {:inline} $Update'$aa_rewarder_Rewarder'_pause(s: $aa_rewarder_Rewarder, x: bool): $aa_rewarder_Rewarder {
    $aa_rewarder_Rewarder(s->$reward_store, s->$emissions_per_second, s->$emissions_per_second_max, s->$emissions_per_liquidity_start, s->$emissions_per_liquidity_latest, s->$user_owed, x)
}
function $IsValid'$aa_rewarder_Rewarder'(s: $aa_rewarder_Rewarder): bool {
    $IsValid'$1_object_Object'$1_fungible_asset_FungibleStore''(s->$reward_store)
      && $IsValid'u64'(s->$emissions_per_second)
      && $IsValid'u64'(s->$emissions_per_second_max)
      && $IsValid'u128'(s->$emissions_per_liquidity_start)
      && $IsValid'u128'(s->$emissions_per_liquidity_latest)
      && $IsValid'u64'(s->$user_owed)
      && $IsValid'bool'(s->$pause)
}
function {:inline} $IsEqual'$aa_rewarder_Rewarder'(s1: $aa_rewarder_Rewarder, s2: $aa_rewarder_Rewarder): bool {
    s1 == s2
}

// struct rewarder::RewarderManager at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/rewarder.move:21:5+129
datatype $aa_rewarder_RewarderManager {
    $aa_rewarder_RewarderManager($rewarders: Vec ($aa_rewarder_Rewarder), $last_updated_time: int, $pause: bool)
}
function {:inline} $Update'$aa_rewarder_RewarderManager'_rewarders(s: $aa_rewarder_RewarderManager, x: Vec ($aa_rewarder_Rewarder)): $aa_rewarder_RewarderManager {
    $aa_rewarder_RewarderManager(x, s->$last_updated_time, s->$pause)
}
function {:inline} $Update'$aa_rewarder_RewarderManager'_last_updated_time(s: $aa_rewarder_RewarderManager, x: int): $aa_rewarder_RewarderManager {
    $aa_rewarder_RewarderManager(s->$rewarders, x, s->$pause)
}
function {:inline} $Update'$aa_rewarder_RewarderManager'_pause(s: $aa_rewarder_RewarderManager, x: bool): $aa_rewarder_RewarderManager {
    $aa_rewarder_RewarderManager(s->$rewarders, s->$last_updated_time, x)
}
function $IsValid'$aa_rewarder_RewarderManager'(s: $aa_rewarder_RewarderManager): bool {
    $IsValid'vec'$aa_rewarder_Rewarder''(s->$rewarders)
      && $IsValid'u64'(s->$last_updated_time)
      && $IsValid'bool'(s->$pause)
}
function {:inline} $IsEqual'$aa_rewarder_RewarderManager'(s1: $aa_rewarder_RewarderManager, s2: $aa_rewarder_RewarderManager): bool {
    $IsEqual'vec'$aa_rewarder_Rewarder''(s1->$rewarders, s2->$rewarders)
    && $IsEqual'u64'(s1->$last_updated_time, s2->$last_updated_time)
    && $IsEqual'bool'(s1->$pause, s2->$pause)}

// struct position_blacklist::PositionBlackList at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/position_blacklist.move:7:5+82
datatype $aa_position_blacklist_PositionBlackList {
    $aa_position_blacklist_PositionBlackList($addresses: $1_smart_vector_SmartVector'address')
}
function {:inline} $Update'$aa_position_blacklist_PositionBlackList'_addresses(s: $aa_position_blacklist_PositionBlackList, x: $1_smart_vector_SmartVector'address'): $aa_position_blacklist_PositionBlackList {
    $aa_position_blacklist_PositionBlackList(x)
}
function $IsValid'$aa_position_blacklist_PositionBlackList'(s: $aa_position_blacklist_PositionBlackList): bool {
    $IsValid'$1_smart_vector_SmartVector'address''(s->$addresses)
}
function {:inline} $IsEqual'$aa_position_blacklist_PositionBlackList'(s1: $aa_position_blacklist_PositionBlackList, s2: $aa_position_blacklist_PositionBlackList): bool {
    $IsEqual'$1_smart_vector_SmartVector'address''(s1->$addresses, s2->$addresses)}

// struct lp::LPTokenRefs at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/lp.move:18:5+160
datatype $aa_lp_LPTokenRefs {
    $aa_lp_LPTokenRefs($burn_ref: $1_fungible_asset_BurnRef, $mint_ref: $1_fungible_asset_MintRef, $transfer_ref: $1_fungible_asset_TransferRef, $extend_ref: $1_object_ExtendRef)
}
function {:inline} $Update'$aa_lp_LPTokenRefs'_burn_ref(s: $aa_lp_LPTokenRefs, x: $1_fungible_asset_BurnRef): $aa_lp_LPTokenRefs {
    $aa_lp_LPTokenRefs(x, s->$mint_ref, s->$transfer_ref, s->$extend_ref)
}
function {:inline} $Update'$aa_lp_LPTokenRefs'_mint_ref(s: $aa_lp_LPTokenRefs, x: $1_fungible_asset_MintRef): $aa_lp_LPTokenRefs {
    $aa_lp_LPTokenRefs(s->$burn_ref, x, s->$transfer_ref, s->$extend_ref)
}
function {:inline} $Update'$aa_lp_LPTokenRefs'_transfer_ref(s: $aa_lp_LPTokenRefs, x: $1_fungible_asset_TransferRef): $aa_lp_LPTokenRefs {
    $aa_lp_LPTokenRefs(s->$burn_ref, s->$mint_ref, x, s->$extend_ref)
}
function {:inline} $Update'$aa_lp_LPTokenRefs'_extend_ref(s: $aa_lp_LPTokenRefs, x: $1_object_ExtendRef): $aa_lp_LPTokenRefs {
    $aa_lp_LPTokenRefs(s->$burn_ref, s->$mint_ref, s->$transfer_ref, x)
}
function $IsValid'$aa_lp_LPTokenRefs'(s: $aa_lp_LPTokenRefs): bool {
    $IsValid'$1_fungible_asset_BurnRef'(s->$burn_ref)
      && $IsValid'$1_fungible_asset_MintRef'(s->$mint_ref)
      && $IsValid'$1_fungible_asset_TransferRef'(s->$transfer_ref)
      && $IsValid'$1_object_ExtendRef'(s->$extend_ref)
}
function {:inline} $IsEqual'$aa_lp_LPTokenRefs'(s1: $aa_lp_LPTokenRefs, s2: $aa_lp_LPTokenRefs): bool {
    s1 == s2
}
var $aa_lp_LPTokenRefs_$memory: $Memory $aa_lp_LPTokenRefs;

// struct pool_v3::LiquidityPoolV3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:71:5+1544
datatype $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3($token_a_liquidity: $1_object_Object'$1_fungible_asset_FungibleStore', $token_b_liquidity: $1_object_Object'$1_fungible_asset_FungibleStore', $token_a_fee: $1_object_Object'$1_fungible_asset_FungibleStore', $token_b_fee: $1_object_Object'$1_fungible_asset_FungibleStore', $sqrt_price: int, $liquidity: int, $tick: $aa_i32_I32, $observation_index: int, $observation_cardinality: int, $observation_cardinality_next: int, $fee_rate: int, $fee_protocol: int, $unlocked: bool, $fee_growth_global_a: int, $fee_growth_global_b: int, $seconds_per_liquidity_oracle: int, $seconds_per_liquidity_incentive: int, $position_blacklist: $aa_position_blacklist_PositionBlackList, $last_update_timestamp: int, $tick_info: Table int ($aa_tick_TickInfo), $tick_map: $aa_tick_bitmap_BitMap, $tick_spacing: int, $protocol_fees: $aa_pool_v3_ProtocolFees, $lp_token_refs: $aa_lp_LPTokenRefs, $max_liquidity_per_tick: int, $rewarder_manager: $aa_rewarder_RewarderManager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_token_a_liquidity(s: $aa_pool_v3_LiquidityPoolV3, x: $1_object_Object'$1_fungible_asset_FungibleStore'): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(x, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_token_b_liquidity(s: $aa_pool_v3_LiquidityPoolV3, x: $1_object_Object'$1_fungible_asset_FungibleStore'): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, x, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_token_a_fee(s: $aa_pool_v3_LiquidityPoolV3, x: $1_object_Object'$1_fungible_asset_FungibleStore'): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, x, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_token_b_fee(s: $aa_pool_v3_LiquidityPoolV3, x: $1_object_Object'$1_fungible_asset_FungibleStore'): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, x, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_sqrt_price(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, x, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_liquidity(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, x, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_tick(s: $aa_pool_v3_LiquidityPoolV3, x: $aa_i32_I32): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, x, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_observation_index(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, x, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_observation_cardinality(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, x, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_observation_cardinality_next(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, x, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_fee_rate(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, x, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_fee_protocol(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, x, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_unlocked(s: $aa_pool_v3_LiquidityPoolV3, x: bool): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, x, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_fee_growth_global_a(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, x, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_fee_growth_global_b(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, x, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_seconds_per_liquidity_oracle(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, x, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_seconds_per_liquidity_incentive(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, x, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_position_blacklist(s: $aa_pool_v3_LiquidityPoolV3, x: $aa_position_blacklist_PositionBlackList): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, x, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_last_update_timestamp(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, x, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_tick_info(s: $aa_pool_v3_LiquidityPoolV3, x: Table int ($aa_tick_TickInfo)): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, x, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_tick_map(s: $aa_pool_v3_LiquidityPoolV3, x: $aa_tick_bitmap_BitMap): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, x, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_tick_spacing(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, x, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_protocol_fees(s: $aa_pool_v3_LiquidityPoolV3, x: $aa_pool_v3_ProtocolFees): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, x, s->$lp_token_refs, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_lp_token_refs(s: $aa_pool_v3_LiquidityPoolV3, x: $aa_lp_LPTokenRefs): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, x, s->$max_liquidity_per_tick, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_max_liquidity_per_tick(s: $aa_pool_v3_LiquidityPoolV3, x: int): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, x, s->$rewarder_manager)
}
function {:inline} $Update'$aa_pool_v3_LiquidityPoolV3'_rewarder_manager(s: $aa_pool_v3_LiquidityPoolV3, x: $aa_rewarder_RewarderManager): $aa_pool_v3_LiquidityPoolV3 {
    $aa_pool_v3_LiquidityPoolV3(s->$token_a_liquidity, s->$token_b_liquidity, s->$token_a_fee, s->$token_b_fee, s->$sqrt_price, s->$liquidity, s->$tick, s->$observation_index, s->$observation_cardinality, s->$observation_cardinality_next, s->$fee_rate, s->$fee_protocol, s->$unlocked, s->$fee_growth_global_a, s->$fee_growth_global_b, s->$seconds_per_liquidity_oracle, s->$seconds_per_liquidity_incentive, s->$position_blacklist, s->$last_update_timestamp, s->$tick_info, s->$tick_map, s->$tick_spacing, s->$protocol_fees, s->$lp_token_refs, s->$max_liquidity_per_tick, x)
}
function $IsValid'$aa_pool_v3_LiquidityPoolV3'(s: $aa_pool_v3_LiquidityPoolV3): bool {
    $IsValid'$1_object_Object'$1_fungible_asset_FungibleStore''(s->$token_a_liquidity)
      && $IsValid'$1_object_Object'$1_fungible_asset_FungibleStore''(s->$token_b_liquidity)
      && $IsValid'$1_object_Object'$1_fungible_asset_FungibleStore''(s->$token_a_fee)
      && $IsValid'$1_object_Object'$1_fungible_asset_FungibleStore''(s->$token_b_fee)
      && $IsValid'u128'(s->$sqrt_price)
      && $IsValid'u128'(s->$liquidity)
      && $IsValid'$aa_i32_I32'(s->$tick)
      && $IsValid'u64'(s->$observation_index)
      && $IsValid'u64'(s->$observation_cardinality)
      && $IsValid'u64'(s->$observation_cardinality_next)
      && $IsValid'u64'(s->$fee_rate)
      && $IsValid'u64'(s->$fee_protocol)
      && $IsValid'bool'(s->$unlocked)
      && $IsValid'u128'(s->$fee_growth_global_a)
      && $IsValid'u128'(s->$fee_growth_global_b)
      && $IsValid'u128'(s->$seconds_per_liquidity_oracle)
      && $IsValid'u128'(s->$seconds_per_liquidity_incentive)
      && $IsValid'$aa_position_blacklist_PositionBlackList'(s->$position_blacklist)
      && $IsValid'u64'(s->$last_update_timestamp)
      && $IsValid'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(s->$tick_info)
      && $IsValid'$aa_tick_bitmap_BitMap'(s->$tick_map)
      && $IsValid'u32'(s->$tick_spacing)
      && $IsValid'$aa_pool_v3_ProtocolFees'(s->$protocol_fees)
      && $IsValid'$aa_lp_LPTokenRefs'(s->$lp_token_refs)
      && $IsValid'u128'(s->$max_liquidity_per_tick)
      && $IsValid'$aa_rewarder_RewarderManager'(s->$rewarder_manager)
}
function {:inline} $IsEqual'$aa_pool_v3_LiquidityPoolV3'(s1: $aa_pool_v3_LiquidityPoolV3, s2: $aa_pool_v3_LiquidityPoolV3): bool {
    $IsEqual'$1_object_Object'$1_fungible_asset_FungibleStore''(s1->$token_a_liquidity, s2->$token_a_liquidity)
    && $IsEqual'$1_object_Object'$1_fungible_asset_FungibleStore''(s1->$token_b_liquidity, s2->$token_b_liquidity)
    && $IsEqual'$1_object_Object'$1_fungible_asset_FungibleStore''(s1->$token_a_fee, s2->$token_a_fee)
    && $IsEqual'$1_object_Object'$1_fungible_asset_FungibleStore''(s1->$token_b_fee, s2->$token_b_fee)
    && $IsEqual'u128'(s1->$sqrt_price, s2->$sqrt_price)
    && $IsEqual'u128'(s1->$liquidity, s2->$liquidity)
    && $IsEqual'$aa_i32_I32'(s1->$tick, s2->$tick)
    && $IsEqual'u64'(s1->$observation_index, s2->$observation_index)
    && $IsEqual'u64'(s1->$observation_cardinality, s2->$observation_cardinality)
    && $IsEqual'u64'(s1->$observation_cardinality_next, s2->$observation_cardinality_next)
    && $IsEqual'u64'(s1->$fee_rate, s2->$fee_rate)
    && $IsEqual'u64'(s1->$fee_protocol, s2->$fee_protocol)
    && $IsEqual'bool'(s1->$unlocked, s2->$unlocked)
    && $IsEqual'u128'(s1->$fee_growth_global_a, s2->$fee_growth_global_a)
    && $IsEqual'u128'(s1->$fee_growth_global_b, s2->$fee_growth_global_b)
    && $IsEqual'u128'(s1->$seconds_per_liquidity_oracle, s2->$seconds_per_liquidity_oracle)
    && $IsEqual'u128'(s1->$seconds_per_liquidity_incentive, s2->$seconds_per_liquidity_incentive)
    && $IsEqual'$aa_position_blacklist_PositionBlackList'(s1->$position_blacklist, s2->$position_blacklist)
    && $IsEqual'u64'(s1->$last_update_timestamp, s2->$last_update_timestamp)
    && $IsEqual'$1_smart_table_SmartTable'$aa_i32_I32_$aa_tick_TickInfo''(s1->$tick_info, s2->$tick_info)
    && $IsEqual'$aa_tick_bitmap_BitMap'(s1->$tick_map, s2->$tick_map)
    && $IsEqual'u32'(s1->$tick_spacing, s2->$tick_spacing)
    && $IsEqual'$aa_pool_v3_ProtocolFees'(s1->$protocol_fees, s2->$protocol_fees)
    && $IsEqual'$aa_lp_LPTokenRefs'(s1->$lp_token_refs, s2->$lp_token_refs)
    && $IsEqual'u128'(s1->$max_liquidity_per_tick, s2->$max_liquidity_per_tick)
    && $IsEqual'$aa_rewarder_RewarderManager'(s1->$rewarder_manager, s2->$rewarder_manager)}
var $aa_pool_v3_LiquidityPoolV3_$memory: $Memory $aa_pool_v3_LiquidityPoolV3;

// struct pool_v3::ProtocolFees at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:110:5+115
datatype $aa_pool_v3_ProtocolFees {
    $aa_pool_v3_ProtocolFees($token_a: $1_object_Object'$1_fungible_asset_FungibleStore', $token_b: $1_object_Object'$1_fungible_asset_FungibleStore')
}
function {:inline} $Update'$aa_pool_v3_ProtocolFees'_token_a(s: $aa_pool_v3_ProtocolFees, x: $1_object_Object'$1_fungible_asset_FungibleStore'): $aa_pool_v3_ProtocolFees {
    $aa_pool_v3_ProtocolFees(x, s->$token_b)
}
function {:inline} $Update'$aa_pool_v3_ProtocolFees'_token_b(s: $aa_pool_v3_ProtocolFees, x: $1_object_Object'$1_fungible_asset_FungibleStore'): $aa_pool_v3_ProtocolFees {
    $aa_pool_v3_ProtocolFees(s->$token_a, x)
}
function $IsValid'$aa_pool_v3_ProtocolFees'(s: $aa_pool_v3_ProtocolFees): bool {
    $IsValid'$1_object_Object'$1_fungible_asset_FungibleStore''(s->$token_a)
      && $IsValid'$1_object_Object'$1_fungible_asset_FungibleStore''(s->$token_b)
}
function {:inline} $IsEqual'$aa_pool_v3_ProtocolFees'(s1: $aa_pool_v3_ProtocolFees, s2: $aa_pool_v3_ProtocolFees): bool {
    s1 == s2
}

// fun pool_v3::dividen_from_pool [verification] at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1764:5+3739
procedure {:timeLimit 40} $aa_pool_v3_dividen_from_pool$verify(_$t0: $Mutation ($aa_pool_v3_LiquidityPoolV3), _$t1: $aa_i32_I32, _$t2: $aa_i32_I32, _$t3: int) returns ($ret0: int, $ret1: int, $ret2: int, $ret3: $1_option_Option'$1_fungible_asset_FungibleAsset', $ret4: $1_option_Option'$1_fungible_asset_FungibleAsset', $ret5: $Mutation ($aa_pool_v3_LiquidityPoolV3))
{
    // declare local variables
    var $t4: $1_option_Option'$1_fungible_asset_FungibleAsset';
    var $t5: $1_option_Option'$1_fungible_asset_FungibleAsset';
    var $t6: int;
    var $t7: int;
    var $t8: $aa_pool_v3_LiquidityPoolV3;
    var $t9: $1_option_Option'$1_fungible_asset_FungibleAsset';
    var $t10: $1_option_Option'$1_fungible_asset_FungibleAsset';
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: bool;
    var $t15: $aa_i32_I32;
    var $t16: bool;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: bool;
    var $t21: int;
    var $t22: $aa_i32_I32;
    var $t23: bool;
    var $t24: int;
    var $t25: int;
    var $t26: bool;
    var $t27: int;
    var $t28: int;
    var $t29: int;
    var $t30: $Mutation (int);
    var $t31: int;
    var $t32: int;
    var $t33: bool;
    var $t34: int;
    var $t0: $Mutation ($aa_pool_v3_LiquidityPoolV3);
    var $t1: $aa_i32_I32;
    var $t2: $aa_i32_I32;
    var $t3: int;
    var $temp_0'$1_option_Option'$1_fungible_asset_FungibleAsset'': $1_option_Option'$1_fungible_asset_FungibleAsset';
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'$aa_pool_v3_LiquidityPoolV3': $aa_pool_v3_LiquidityPoolV3;
    var $temp_0'u128': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume And(WellFormed($t0), And(And(And(And(And(And(Or(option::$is_none<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), And(option::$is_some<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), Neq<u64>(option::$borrow<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), 0))), Or(option::$is_none<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), Le(Len<address>(select smart_vector::SmartVector.inline_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$borrow<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))))), Or(And(option::$is_none<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$is_none<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), And(option::$is_some<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$is_some<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))))), Le(Len<0x1::big_vector::BigVector<address>>(select option::Option.vec(select smart_vector::SmartVector.big_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1)), forall $elem: 0x1::big_vector::BigVector<address>: select option::Option.vec(select smart_vector::SmartVector.big_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))): And(And(And(And(And(And(And(And(And(And(And(Neq<u64>(select big_vector::BigVector.bucket_size($elem), 0), Implies(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<u64>(select big_vector::BigVector.end_index($elem), 0))), Implies(Eq<u64>(select big_vector::BigVector.end_index($elem), 0), Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0))), Le(select big_vector::BigVector.end_index($elem), Mul(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), select big_vector::BigVector.bucket_size($elem)))), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), forall i: num: Range(0, Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1)): Eq<num>(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), select big_vector::BigVector.bucket_size($elem)))), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Le(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1))), select big_vector::BigVector.bucket_size($elem)))), forall i: num: Range(0, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), Div(Sub(Add(select big_vector::BigVector.end_index($elem), select big_vector::BigVector.bucket_size($elem)), 1), select big_vector::BigVector.bucket_size($elem)))), Or(And(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<u64>(select big_vector::BigVector.end_index($elem), 0)), And(Neq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<num>(Add(Mul(Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1), select big_vector::BigVector.bucket_size($elem)), Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1)))), select big_vector::BigVector.end_index($elem))))), forall i: u64: TypeDomain<u64>() where Ge(i, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): Not(big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i))), forall i: u64: TypeDomain<u64>() where Lt(i, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Gt(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1))), 0)))), Le(Len<u64>(select option::Option.vec(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1)), Le(Len<u64>(select option::Option.vec(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1))) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1764:5+1
    assume {:print "$at(19,68377,68378)"} true;
    assume ($IsValid'$aa_pool_v3_LiquidityPoolV3'($Dereference($t0)) && ((((((($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size) || ($1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size) && !$IsEqual'u64'($1_option_$borrow'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size), 0))) && ($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) || (LenVec($Dereference($t0)->$position_blacklist->$addresses->$inline_vec) <= $1_option_$borrow'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity)))) && (($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) && $1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size)) || ($1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) && $1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size)))) && (LenVec($Dereference($t0)->$position_blacklist->$addresses->$big_vec->$vec) <= 1)) && (var $range_0 := $Dereference($t0)->$position_blacklist->$addresses->$big_vec->$vec; (forall $i_1: int :: InRangeVec($range_0, $i_1) ==> (var $elem := ReadVec($range_0, $i_1);
    ((((((((((((!$IsEqual'u64'($elem->$bucket_size, 0) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) ==> $IsEqual'u64'($elem->$end_index, 0))) && ($IsEqual'u64'($elem->$end_index, 0) ==> $IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0))) && ($elem->$end_index <= ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) * $elem->$bucket_size))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (var $range_2 := $Range(0, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1)); (forall $i_3: int :: $InRange($range_2, $i_3) ==> (var i := $i_3;
    ($IsEqual'num'(LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, i)), $elem->$bucket_size))))))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1))) <= $elem->$bucket_size))) && (var $range_4 := $Range(0, $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)); (forall $i_5: int :: $InRange($range_4, $i_5) ==> (var i := $i_5;
    ($1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))))) && $IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), ((($elem->$end_index + $elem->$bucket_size) - 1) div $elem->$bucket_size))) && (($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) && $IsEqual'u64'($elem->$end_index, 0)) || (!$IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) && $IsEqual'num'(((($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1) * $elem->$bucket_size) + LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1)))), $elem->$end_index)))) && (forall i: int :: $IsValid'u64'(i) ==> ((i >= $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)))  ==> (!$1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))) && (forall i: int :: $IsValid'u64'(i) ==> ((i < $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)))  ==> ($1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1))) > 0)))))))) && (LenVec($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity->$vec) <= 1)) && (LenVec($Dereference($t0)->$position_blacklist->$addresses->$bucket_size->$vec) <= 1)));

    // assume WellFormed($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1764:5+1
    assume $IsValid'$aa_i32_I32'($t1);

    // assume WellFormed($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1764:5+1
    assume $IsValid'$aa_i32_I32'($t2);

    // assume WellFormed($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1764:5+1
    assume $IsValid'u128'($t3);

    // assume Lt(i32::$as_u32($t1), i32::$as_u32($t2)) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1846:5+59
    assume {:print "$at(19,72322,72381)"} true;
    assume $Lt'Bv32'($aa_i32_$as_u32($t1), $aa_i32_$as_u32($t2));

    // $t8 := read_ref($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1846:5+59
    $t8 := $Dereference($t0);

    // trace_local[pool]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1764:5+1
    assume {:print "$at(19,68377,68378)"} true;
    $temp_0'$aa_pool_v3_LiquidityPoolV3' := $Dereference($t0);
    assume {:print "$track_local(118,37,0):", $temp_0'$aa_pool_v3_LiquidityPoolV3'} $temp_0'$aa_pool_v3_LiquidityPoolV3' == $temp_0'$aa_pool_v3_LiquidityPoolV3';

    // trace_local[tick_lower]($t1) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1764:5+1
    assume {:print "$track_local(118,37,1):", $t1} $t1 == $t1;

    // trace_local[tick_upper]($t2) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1764:5+1
    assume {:print "$track_local(118,37,2):", $t2} $t2 == $t2;

    // trace_local[liquidity_delta]($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1764:5+1
    assume {:print "$track_local(118,37,3):", $t3} $t3 == $t3;

    // $t9 := opaque begin: option::none<0x1::fungible_asset::FungibleAsset>() at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1770:24+29
    assume {:print "$at(19,68612,68641)"} true;

    // assume And(WellFormed($t9), Le(Len<0x1::fungible_asset::FungibleAsset>(select option::Option.vec($t9)), 1)) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1770:24+29
    assume ($IsValid'$1_option_Option'$1_fungible_asset_FungibleAsset''($t9) && (LenVec($t9->$vec) <= 1));

    // assume Eq<0x1::option::Option<0x1::fungible_asset::FungibleAsset>>($t9, option::spec_none<0x1::fungible_asset::FungibleAsset>()) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1770:24+29
    assume $IsEqual'$1_option_Option'$1_fungible_asset_FungibleAsset''($t9, $1_option_spec_none'$1_fungible_asset_FungibleAsset'());

    // $t9 := opaque end: option::none<0x1::fungible_asset::FungibleAsset>() at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1770:24+29

    // trace_local[fa_a_opt]($t9) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1770:24+29
    assume {:print "$track_local(118,37,4):", $t9} $t9 == $t9;

    // $t10 := opaque begin: option::none<0x1::fungible_asset::FungibleAsset>() at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1771:24+29
    assume {:print "$at(19,68666,68695)"} true;

    // assume And(WellFormed($t10), Le(Len<0x1::fungible_asset::FungibleAsset>(select option::Option.vec($t10)), 1)) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1771:24+29
    assume ($IsValid'$1_option_Option'$1_fungible_asset_FungibleAsset''($t10) && (LenVec($t10->$vec) <= 1));

    // assume Eq<0x1::option::Option<0x1::fungible_asset::FungibleAsset>>($t10, option::spec_none<0x1::fungible_asset::FungibleAsset>()) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1771:24+29
    assume $IsEqual'$1_option_Option'$1_fungible_asset_FungibleAsset''($t10, $1_option_spec_none'$1_fungible_asset_FungibleAsset'());

    // $t10 := opaque end: option::none<0x1::fungible_asset::FungibleAsset>() at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1771:24+29

    // trace_local[fa_b_opt]($t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1771:24+29
    assume {:print "$track_local(118,37,5):", $t10} $t10 == $t10;

    // $t11 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1772:37+1
    assume {:print "$at(19,68733,68734)"} true;
    $t11 := 0;
    assume $IsValid'u64'($t11);

    // $t6 := $t11 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1772:37+1
    $t6 := $t11;

    // trace_local[$t13]($t11) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1772:37+1
    assume {:print "$track_local(118,37,6):", $t11} $t11 == $t11;

    // $t12 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1772:40+1
    $t12 := 0;
    assume $IsValid'u64'($t12);

    // $t7 := $t12 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1772:40+1
    $t7 := $t12;

    // trace_local[$t14]($t12) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1772:40+1
    assume {:print "$track_local(118,37,7):", $t12} $t12 == $t12;

    // $t13 := 0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1773:32+1
    assume {:print "$at(19,68771,68772)"} true;
    $t13 := 0;
    assume $IsValid'u128'($t13);

    // $t14 := !=($t3, $t13) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1773:13+20
    $t14 := !$IsEqual'u128'($t3, $t13);

    // if ($t14) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1773:9+3295
    if ($t14) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1774:25+9
    assume {:print "$at(19,68800,68809)"} true;
L1:

    // $t15 := get_field<0xaa::pool_v3::LiquidityPoolV3>.tick($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1774:25+9
    assume {:print "$at(19,68800,68809)"} true;
    $t15 := $Dereference($t0)->$tick;

    // $t16 := i32::lt($t15, $t1) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1774:17+30
    call $t16 := $aa_i32_lt($t15, $t1);
    if ($abort_flag) {
        assume {:print "$at(19,68792,68822)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // if ($t16) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1774:13+3244
    if ($t16) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1774:49+759
L3:

    // drop($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1774:49+759
    assume {:print "$at(19,68824,69583)"} true;

    // $t18 := tick_math::get_sqrt_price_at_tick($t1) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1778:21+45
    assume {:print "$at(19,69126,69171)"} true;
    call $t18 := $aa_tick_math_get_sqrt_price_at_tick($t1);
    if ($abort_flag) {
        assume {:print "$at(19,69126,69171)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // $t19 := tick_math::get_sqrt_price_at_tick($t2) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1779:21+45
    assume {:print "$at(19,69193,69238)"} true;
    call $t19 := $aa_tick_math_get_sqrt_price_at_tick($t2);
    if ($abort_flag) {
        assume {:print "$at(19,69193,69238)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // $t20 := false at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1781:21+5
    assume {:print "$at(19,69297,69302)"} true;
    $t20 := false;
    assume $IsValid'bool'($t20);

    // $t21 := swap_math::get_delta_a($t18, $t19, $t3, $t20) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1777:28+238
    assume {:print "$at(19,69082,69320)"} true;
    call $t21 := $aa_swap_math_get_delta_a($t18, $t19, $t3, $t20);
    if ($abort_flag) {
        assume {:print "$at(19,69082,69320)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // $t6 := $t21 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1777:17+249
    $t6 := $t21;

    // trace_local[$t13]($t21) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1777:17+249
    assume {:print "$track_local(118,37,6):", $t21} $t21 == $t21;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1838:10+15
    assume {:print "$at(19,72054,72069)"} true;
L6:

    // trace_return[0]($t3) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1769:71+3529
    assume {:print "$at(19,68587,72116)"} true;
    assume {:print "$track_return(118,37,0):", $t3} $t3 == $t3;

    // trace_return[1]($t6) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1769:71+3529
    assume {:print "$track_return(118,37,1):", $t6} $t6 == $t6;

    // trace_return[2]($t7) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1769:71+3529
    assume {:print "$track_return(118,37,2):", $t7} $t7 == $t7;

    // trace_return[3]($t9) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1769:71+3529
    assume {:print "$track_return(118,37,3):", $t9} $t9 == $t9;

    // trace_return[4]($t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1769:71+3529
    assume {:print "$track_return(118,37,4):", $t10} $t10 == $t10;

    // trace_local[pool]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1769:71+3529
    $temp_0'$aa_pool_v3_LiquidityPoolV3' := $Dereference($t0);
    assume {:print "$track_local(118,37,0):", $temp_0'$aa_pool_v3_LiquidityPoolV3'} $temp_0'$aa_pool_v3_LiquidityPoolV3' == $temp_0'$aa_pool_v3_LiquidityPoolV3';

    // assert Or(option::$is_none<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), And(option::$is_some<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), Neq<u64>(option::$borrow<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), 0))) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:5:9+121
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:5:9+121
    assume {:print "$at(80,118,239)"} true;
    assert {:msg "assert_failed(80,118,239): data invariant does not hold"}
      ($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size) || ($1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size) && !$IsEqual'u64'($1_option_$borrow'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size), 0)));

    // assert Or(option::$is_none<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), Le(Len<address>(select smart_vector::SmartVector.inline_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$borrow<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))))) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:8:9+111
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:8:9+111
    assume {:print "$at(80,319,430)"} true;
    assert {:msg "assert_failed(80,319,430): data invariant does not hold"}
      ($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) || (LenVec($Dereference($t0)->$position_blacklist->$addresses->$inline_vec) <= $1_option_$borrow'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity)));

    // assert Or(And(option::$is_none<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$is_none<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), And(option::$is_some<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$is_some<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))))) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:11:9+159
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:11:9+159
    assume {:print "$at(80,538,697)"} true;
    assert {:msg "assert_failed(80,538,697): data invariant does not hold"}
      (($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) && $1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size)) || ($1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) && $1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size)));

    // assert Le(Len<0x1::big_vector::BigVector<address>>(select option::Option.vec(select smart_vector::SmartVector.big_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    assume {:print "$at(39,530,554)"} true;
    assert {:msg "assert_failed(39,530,554): data invariant does not hold"}
      (LenVec($Dereference($t0)->$position_blacklist->$addresses->$big_vec->$vec) <= 1);

    // assert forall $elem: 0x1::big_vector::BigVector<address>: select option::Option.vec(select smart_vector::SmartVector.big_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))): And(And(And(And(And(And(And(And(And(And(And(Neq<u64>(select big_vector::BigVector.bucket_size($elem), 0), Implies(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<u64>(select big_vector::BigVector.end_index($elem), 0))), Implies(Eq<u64>(select big_vector::BigVector.end_index($elem), 0), Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0))), Le(select big_vector::BigVector.end_index($elem), Mul(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), select big_vector::BigVector.bucket_size($elem)))), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), forall i: num: Range(0, Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1)): Eq<num>(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), select big_vector::BigVector.bucket_size($elem)))), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Le(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1))), select big_vector::BigVector.bucket_size($elem)))), forall i: num: Range(0, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), Div(Sub(Add(select big_vector::BigVector.end_index($elem), select big_vector::BigVector.bucket_size($elem)), 1), select big_vector::BigVector.bucket_size($elem)))), Or(And(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<u64>(select big_vector::BigVector.end_index($elem), 0)), And(Neq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<num>(Add(Mul(Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1), select big_vector::BigVector.bucket_size($elem)), Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1)))), select big_vector::BigVector.end_index($elem))))), forall i: u64: TypeDomain<u64>() where Ge(i, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): Not(big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i))), forall i: u64: TypeDomain<u64>() where Lt(i, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Gt(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1))), 0))) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/big_vector.spec.move:7:9+27
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/big_vector.spec.move:7:9+27
    assume {:print "$at(76,132,159)"} true;
    assert {:msg "assert_failed(76,132,159): data invariant does not hold"}
      (var $range_0 := $Dereference($t0)->$position_blacklist->$addresses->$big_vec->$vec; (forall $i_1: int :: InRangeVec($range_0, $i_1) ==> (var $elem := ReadVec($range_0, $i_1);
    ((((((((((((!$IsEqual'u64'($elem->$bucket_size, 0) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) ==> $IsEqual'u64'($elem->$end_index, 0))) && ($IsEqual'u64'($elem->$end_index, 0) ==> $IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0))) && ($elem->$end_index <= ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) * $elem->$bucket_size))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (var $range_2 := $Range(0, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1)); (forall $i_3: int :: $InRange($range_2, $i_3) ==> (var i := $i_3;
    ($IsEqual'num'(LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, i)), $elem->$bucket_size))))))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1))) <= $elem->$bucket_size))) && (var $range_4 := $Range(0, $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)); (forall $i_5: int :: $InRange($range_4, $i_5) ==> (var i := $i_5;
    ($1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))))) && $IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), ((($elem->$end_index + $elem->$bucket_size) - 1) div $elem->$bucket_size))) && (($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) && $IsEqual'u64'($elem->$end_index, 0)) || (!$IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) && $IsEqual'num'(((($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1) * $elem->$bucket_size) + LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1)))), $elem->$end_index)))) && (forall i: int :: $IsValid'u64'(i) ==> ((i >= $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)))  ==> (!$1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))) && (forall i: int :: $IsValid'u64'(i) ==> ((i < $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)))  ==> ($1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1))) > 0)))))));

    // assert Le(Len<u64>(select option::Option.vec(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    assume {:print "$at(39,530,554)"} true;
    assert {:msg "assert_failed(39,530,554): data invariant does not hold"}
      (LenVec($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity->$vec) <= 1);

    // assert Le(Len<u64>(select option::Option.vec(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    assert {:msg "assert_failed(39,530,554): data invariant does not hold"}
      (LenVec($Dereference($t0)->$position_blacklist->$addresses->$bucket_size->$vec) <= 1);

    // goto L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1769:71+3529
    assume {:print "$at(19,68587,72116)"} true;
    goto L7;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1787:32+9
    assume {:print "$at(19,69601,69610)"} true;
L2:

    // $t22 := get_field<0xaa::pool_v3::LiquidityPoolV3>.tick($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1787:32+9
    assume {:print "$at(19,69601,69610)"} true;
    $t22 := $Dereference($t0)->$tick;

    // $t23 := i32::lt($t22, $t2) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1787:24+30
    call $t23 := $aa_i32_lt($t22, $t2);
    if ($abort_flag) {
        assume {:print "$at(19,69593,69623)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // if ($t23) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1787:20+2443
    if ($t23) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1803:21+15
    assume {:print "$at(19,70312,70327)"} true;
L5:

    // $t24 := get_field<0xaa::pool_v3::LiquidityPoolV3>.sqrt_price($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1803:21+15
    assume {:print "$at(19,70312,70327)"} true;
    $t24 := $Dereference($t0)->$sqrt_price;

    // $t25 := tick_math::get_sqrt_price_at_tick($t2) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1804:21+45
    assume {:print "$at(19,70349,70394)"} true;
    call $t25 := $aa_tick_math_get_sqrt_price_at_tick($t2);
    if ($abort_flag) {
        assume {:print "$at(19,70349,70394)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // $t26 := false at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1806:21+5
    assume {:print "$at(19,70453,70458)"} true;
    $t26 := false;
    assume $IsValid'bool'($t26);

    // $t27 := swap_math::get_delta_a($t24, $t25, $t3, $t26) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1802:28+208
    assume {:print "$at(19,70268,70476)"} true;
    call $t27 := $aa_swap_math_get_delta_a($t24, $t25, $t3, $t26);
    if ($abort_flag) {
        assume {:print "$at(19,70268,70476)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // $t6 := $t27 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1802:17+219
    $t6 := $t27;

    // trace_local[$t13]($t27) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1802:17+219
    assume {:print "$track_local(118,37,6):", $t27} $t27 == $t27;

    // $t28 := get_field<0xaa::pool_v3::LiquidityPoolV3>.liquidity($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1822:60+14
    assume {:print "$at(19,71220,71234)"} true;
    $t28 := $Dereference($t0)->$liquidity;

    // $t29 := liquidity_math::sub_delta($t28, $t3) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1822:34+58
    call $t29 := $aa_liquidity_math_sub_delta($t28, $t3);
    if ($abort_flag) {
        assume {:print "$at(19,71194,71252)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // $t30 := borrow_field<0xaa::pool_v3::LiquidityPoolV3>.liquidity($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1822:17+14
    $t30 := $ChildMutation($t0, 5, $Dereference($t0)->$liquidity);

    // write_ref($t30, $t29) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1822:17+75
    $t30 := $UpdateMutation($t30, $t29);

    // write_back[Reference($t0).liquidity (u128)]($t30) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1822:17+75
    $t0 := $UpdateMutation($t0, $Update'$aa_pool_v3_LiquidityPoolV3'_liquidity($Dereference($t0), $Dereference($t30)));

    // trace_local[pool]($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1822:17+75
    $temp_0'$aa_pool_v3_LiquidityPoolV3' := $Dereference($t0);
    assume {:print "$track_local(118,37,0):", $temp_0'$aa_pool_v3_LiquidityPoolV3'} $temp_0'$aa_pool_v3_LiquidityPoolV3' == $temp_0'$aa_pool_v3_LiquidityPoolV3';

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1787:56+1642
    assume {:print "$at(19,69625,71267)"} true;
    goto L6;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1823:20+759
    assume {:print "$at(19,71273,72032)"} true;
L4:

    // drop($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1823:20+759
    assume {:print "$at(19,71273,72032)"} true;

    // $t31 := tick_math::get_sqrt_price_at_tick($t1) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1827:21+45
    assume {:print "$at(19,71575,71620)"} true;
    call $t31 := $aa_tick_math_get_sqrt_price_at_tick($t1);
    if ($abort_flag) {
        assume {:print "$at(19,71575,71620)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // $t32 := tick_math::get_sqrt_price_at_tick($t2) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1828:21+45
    assume {:print "$at(19,71642,71687)"} true;
    call $t32 := $aa_tick_math_get_sqrt_price_at_tick($t2);
    if ($abort_flag) {
        assume {:print "$at(19,71642,71687)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // $t33 := false at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1830:21+5
    assume {:print "$at(19,71746,71751)"} true;
    $t33 := false;
    assume $IsValid'bool'($t33);

    // $t34 := swap_math::get_delta_b($t31, $t32, $t3, $t33) on_abort goto L8 with $t17 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1826:28+238
    assume {:print "$at(19,71531,71769)"} true;
    call $t34 := $aa_swap_math_get_delta_b($t31, $t32, $t3, $t33);
    if ($abort_flag) {
        assume {:print "$at(19,71531,71769)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(118,37):", $t17} $t17 == $t17;
        goto L8;
    }

    // $t7 := $t34 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1826:17+249
    $t7 := $t34;

    // trace_local[$t14]($t34) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1826:17+249
    assume {:print "$track_local(118,37,7):", $t34} $t34 == $t34;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1826:17+249
    goto L6;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1773:9+3295
    assume {:print "$at(19,68748,72043)"} true;
L0:

    // drop($t0) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1773:9+3295
    assume {:print "$at(19,68748,72043)"} true;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1773:9+3295
    goto L6;

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1839:5+1
    assume {:print "$at(19,72115,72116)"} true;
L7:

    // assert Not(And(And(And(Neq<u128>($t3, 0), Ge(i32::$as_u32[](select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t8)), i32::$as_u32[]($t1))), Lt(i32::$as_u32[](select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t8)), i32::$as_u32[]($t2))), Lt(select pool_v3::LiquidityPoolV3.liquidity<0xaa::pool_v3::LiquidityPoolV3>($t8), $t3))) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1850:5+199
    assume {:print "$at(19,72619,72818)"} true;
    assert {:msg "assert_failed(19,72619,72818): function does not abort under this condition"}
      !(((!$IsEqual'u128'($t3, 0) && $Ge'Bv32'($aa_i32_$as_u32($t8->$tick), $aa_i32_$as_u32($t1))) && $Lt'Bv32'($aa_i32_$as_u32($t8->$tick), $aa_i32_$as_u32($t2))) && ($t8->$liquidity < $t3));

    // assert Implies(And(And(Neq<u128>($t3, 0), Ge(i32::$as_u32(select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t0)), i32::$as_u32($t1))), Lt(i32::$as_u32(select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t0)), i32::$as_u32($t2))), Eq<u128>(select pool_v3::LiquidityPoolV3.liquidity<0xaa::pool_v3::LiquidityPoolV3>($t0), Sub(select pool_v3::LiquidityPoolV3.liquidity<0xaa::pool_v3::LiquidityPoolV3>($t8), $t3))) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1857:5+221
    assume {:print "$at(19,73179,73400)"} true;
    assert {:msg "assert_failed(19,73179,73400): post-condition does not hold"}
      (((!$IsEqual'u128'($t3, 0) && $Ge'Bv32'($aa_i32_$as_u32($Dereference($t0)->$tick), $aa_i32_$as_u32($t1))) && $Lt'Bv32'($aa_i32_$as_u32($Dereference($t0)->$tick), $aa_i32_$as_u32($t2))) ==> $IsEqual'u128'($Dereference($t0)->$liquidity, ($t8->$liquidity - $t3)));

    // assert Implies(Or(Lt(i32::$as_u32(select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t0)), i32::$as_u32($t1)), Ge(i32::$as_u32(select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t0)), i32::$as_u32($t2))), Eq<u128>(select pool_v3::LiquidityPoolV3.liquidity<0xaa::pool_v3::LiquidityPoolV3>($t0), select pool_v3::LiquidityPoolV3.liquidity<0xaa::pool_v3::LiquidityPoolV3>($t8))) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1864:5+174
    assume {:print "$at(19,73740,73914)"} true;
    assert {:msg "assert_failed(19,73740,73914): post-condition does not hold"}
      (($Lt'Bv32'($aa_i32_$as_u32($Dereference($t0)->$tick), $aa_i32_$as_u32($t1)) || $Ge'Bv32'($aa_i32_$as_u32($Dereference($t0)->$tick), $aa_i32_$as_u32($t2))) ==> $IsEqual'u128'($Dereference($t0)->$liquidity, $t8->$liquidity));

    // return ($t3, $t6, $t7, $t9, $t10) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1864:5+174
    $ret0 := $t3;
    $ret1 := $t6;
    $ret2 := $t7;
    $ret3 := $t9;
    $ret4 := $t10;
    $ret5 := $t0;
    return;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1839:5+1
    assume {:print "$at(19,72115,72116)"} true;
L8:

    // abort($t17) at /Users/jackfisher/Desktop/audits/dex-v3-latest/sources/v3/pool_v3.move:1839:5+1
    assume {:print "$at(19,72115,72116)"} true;
    $abort_code := $t17;
    $abort_flag := true;
    return;

}
