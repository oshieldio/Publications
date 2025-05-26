
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

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:171:5+66
function {:inline} $aa_i32_$sign(v: $aa_i32_I32): bv8
{
    v->$bits[31:30] ++ 0bv7 
}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:119:5+231
function {:inline} $aa_i32_$abs(v: $aa_i32_I32): $aa_i32_I32 {
    (if ($IsEqual'bv8'($aa_i32_$sign(v), 0bv8)) then (v) else ($aa_i32_I32($aa_i32_$u32_neg($Sub'Bv32'(v->$bits, 1bv32)))))
}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:167:5+53
function {:inline} $aa_i32_$as_u32(v: $aa_i32_I32): bv32 {
    v->$bits
}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:175:5+60
function {:inline} $aa_i32_$is_neg(v: $aa_i32_I32): bool {
    $IsEqual'bv8'($aa_i32_$sign(v), 1bv8)
}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:244:5+55
function {:inline} $aa_i32_$u32_neg(v: bv32): bv32 {
    $Xor'Bv32'(v, 4294967295bv32)
}

// struct i32::I32 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:11:5+58
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

// fun i32::cmp [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:179:5+299
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
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:179:5+1
    assume {:print "$at(7,3981,3982)"} true;
    assume {:print "$track_local(98,2,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:179:5+1
    assume {:print "$track_local(98,2,1):", $t1} $t1 == $t1;

    // $t2 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:180:13+9
    assume {:print "$at(7,4036,4045)"} true;
$t2 := $bv2int.32($t0->$bits);

    // $t3 := get_field<0xaa::i32::I32>.bits($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:180:26+9
$t3 := $bv2int.32($t1->$bits);

    // $t4 := ==($t2, $t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:180:13+22
    $t4 := $IsEqual'u32'($t2, $t3);

    // if ($t4) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:180:9+37
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:180:44+2
L1:

    // $t5 := 1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:180:44+2
    assume {:print "$at(7,4067,4069)"} true;
    $t5 := 1;
    assume $IsValid'u8'($t5);

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:180:37+9
    assume {:print "$track_return(98,2,0):", $t5} $t5 == $t5;

    // $t6 := move($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:180:37+9
    $t6 := $t5;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:180:37+9
    goto L8;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:13+10
    assume {:print "$at(7,4083,4093)"} true;
L0:

    // $t7 := i32::sign($t0) on_abort goto L9 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:13+10
    assume {:print "$at(7,4083,4093)"} true;
    call $t7 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,4083,4093)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t9 := i32::sign($t1) on_abort goto L9 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:26+10
    call $t9 := $aa_i32_sign($t1);
    if ($abort_flag) {
        assume {:print "$at(7,4096,4106)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t10 := >($t7, $t9) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:13+23
    call $t10 := $Gt($t7, $t9);

    // if ($t10) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:9+38
    if ($t10) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:45+2
L3:

    // $t11 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:45+2
    assume {:print "$at(7,4115,4117)"} true;
    $t11 := 0;
    assume $IsValid'u8'($t11);

    // trace_return[0]($t11) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:38+9
    assume {:print "$track_return(98,2,0):", $t11} $t11 == $t11;

    // $t6 := move($t11) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:38+9
    $t6 := $t11;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:181:38+9
    goto L8;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:13+10
    assume {:print "$at(7,4131,4141)"} true;
L2:

    // $t12 := i32::sign($t0) on_abort goto L9 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:13+10
    assume {:print "$at(7,4131,4141)"} true;
    call $t12 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,4131,4141)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t13 := i32::sign($t1) on_abort goto L9 with $t8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:26+10
    call $t13 := $aa_i32_sign($t1);
    if ($abort_flag) {
        assume {:print "$at(7,4144,4154)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t14 := <($t12, $t13) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:13+23
    call $t14 := $Lt($t12, $t13);

    // if ($t14) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:9+38
    if ($t14) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:45+2
L5:

    // $t15 := 2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:45+2
    assume {:print "$at(7,4163,4165)"} true;
    $t15 := 2;
    assume $IsValid'u8'($t15);

    // trace_return[0]($t15) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:38+9
    assume {:print "$track_return(98,2,0):", $t15} $t15 == $t15;

    // $t6 := move($t15) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:38+9
    $t6 := $t15;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:182:38+9
    goto L8;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:183:13+4
    assume {:print "$at(7,4179,4183)"} true;
L4:

    // $t16 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:183:13+9
    assume {:print "$at(7,4179,4188)"} true;
$t16 := $bv2int.32($t0->$bits);

    // $t17 := get_field<0xaa::i32::I32>.bits($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:183:25+9
$t17 := $bv2int.32($t1->$bits);

    // $t18 := >($t16, $t17) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:183:13+21
    call $t18 := $Gt($t16, $t17);

    // if ($t18) goto L7 else goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:183:9+99
    if ($t18) { goto L7; } else { goto L6; }

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:184:20+2
    assume {:print "$at(7,4223,4225)"} true;
L7:

    // $t19 := 2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:184:20+2
    assume {:print "$at(7,4223,4225)"} true;
    $t19 := 2;
    assume $IsValid'u8'($t19);

    // trace_return[0]($t19) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:184:13+9
    assume {:print "$track_return(98,2,0):", $t19} $t19 == $t19;

    // $t6 := move($t19) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:184:13+9
    $t6 := $t19;

    // goto L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:184:13+9
    goto L8;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:186:20+2
    assume {:print "$at(7,4262,4264)"} true;
L6:

    // $t20 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:186:20+2
    assume {:print "$at(7,4262,4264)"} true;
    $t20 := 0;
    assume $IsValid'u8'($t20);

    // trace_return[0]($t20) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:186:13+9
    assume {:print "$track_return(98,2,0):", $t20} $t20 == $t20;

    // $t6 := move($t20) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:186:13+9
    $t6 := $t20;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:188:5+1
    assume {:print "$at(7,4279,4280)"} true;
L8:

    // return $t6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:188:5+1
    assume {:print "$at(7,4279,4280)"} true;
    $ret0 := $t6;
    return;

    // label L9 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:188:5+1
L9:

    // abort($t8) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:188:5+1
    assume {:print "$at(7,4279,4280)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun i32::sign [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:171:5+66
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
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:171:5+1
    assume {:print "$at(7,3843,3844)"} true;
    assume {:print "$track_local(98,8,0):", $t0} $t0 == $t0;

    // $t1 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:172:11+6
    assume {:print "$at(7,3883,3889)"} true;
$t1 := $bv2int.32($t0->$bits);

    // $t2 := 31 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:172:21+2
    $t2 := 31;
    assume $IsValid'u8'($t2);

    // $t3 := >>($t1, $t2) on_abort goto L2 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:172:10+14
    call $t3 := $ShrU32($t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(7,3882,3896)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(98,8):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := (u8)($t3) on_abort goto L2 with $t4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:172:9+22
    call $t5 := $CastU8($t3);
    if ($abort_flag) {
        assume {:print "$at(7,3881,3903)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(98,8):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:172:9+22
    assume {:print "$track_return(98,8,0):", $t5} $t5 == $t5;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:173:5+1
    assume {:print "$at(7,3908,3909)"} true;
L1:

    // return $t5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:173:5+1
    assume {:print "$at(7,3908,3909)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:173:5+1
L2:

    // abort($t4) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:173:5+1
    assume {:print "$at(7,3908,3909)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun i32::abs [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:119:5+231
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
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:119:5+1
    assume {:print "$at(7,2747,2748)"} true;
    assume {:print "$track_local(98,9,0):", $t0} $t0 == $t0;

    // $t2 := i32::sign($t0) on_abort goto L6 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:120:13+7
    assume {:print "$at(7,2789,2796)"} true;
    call $t2 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,2789,2796)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,9):", $t3} $t3 == $t3;
        goto L6;
    }

    // $t4 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:120:24+1
    $t4 := 0;
    assume $IsValid'u8'($t4);

    // $t5 := ==($t2, $t4) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:120:13+12
    $t5 := $IsEqual'u8'($t2, $t4);

    // if ($t5) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:120:9+187
    if ($t5) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:121:13+1
    assume {:print "$at(7,2817,2818)"} true;
L1:

    // $t1 := $t0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:121:13+1
    assume {:print "$at(7,2817,2818)"} true;
    $t1 := $t0;

    // trace_local[return]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:121:13+1
    assume {:print "$track_local(98,9,1):", $t0} $t0 == $t0;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:120:9+187
    assume {:print "$at(7,2785,2972)"} true;
L4:

    // trace_return[0]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:120:9+187
    assume {:print "$at(7,2785,2972)"} true;
    assume {:print "$track_return(98,9,0):", $t1} $t1 == $t1;

    // goto L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:120:9+187
    goto L5;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:21+1
    assume {:print "$at(7,2856,2857)"} true;
L0:

    // $t6 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:21+6
    assume {:print "$at(7,2856,2862)"} true;
    $t6 := $t0->$bits;

    // $t7 := 2147483648 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:30+10
    $t7 := 2147483648bv32;
    assume $IsValid'bv32'($t7);

    // $t8 := >($t6, $t7) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:21+19
    call $t8 := $GtBv32($t6, $t7);

    // if ($t8) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:13+6
    if ($t8) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:125:31+1
    assume {:print "$at(7,2937,2938)"} true;
L3:

    // $t9 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:125:31+6
    assume {:print "$at(7,2937,2943)"} true;
    $t9 := $t0->$bits;

    // $t10 := 1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:125:40+1
    $t10 := 1bv32;
    assume $IsValid'bv32'($t10);

    // $t11 := -($t9, $t10) on_abort goto L6 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:125:31+10
    call $t11 := $SubBv32($t9, $t10);
    if ($abort_flag) {
        assume {:print "$at(7,2937,2947)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,9):", $t3} $t3 == $t3;
        goto L6;
    }

    // $t12 := i32::u32_neg($t11) on_abort goto L6 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:125:23+19
    call $t12 := $aa_i32_u32_neg($t11);
    if ($abort_flag) {
        assume {:print "$at(7,2929,2948)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,9):", $t3} $t3 == $t3;
        goto L6;
    }

    // $t13 := pack 0xaa::i32::I32($t12) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:124:13+61
    assume {:print "$at(7,2901,2962)"} true;
    $t13 := $aa_i32_I32($t12);

    // $t1 := $t13 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:124:13+61
    $t1 := $t13;

    // trace_local[return]($t13) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:124:13+61
    assume {:print "$track_local(98,9,1):", $t13} $t13 == $t13;

    // goto L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:124:13+61
    goto L4;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:42+9
    assume {:print "$at(7,2877,2886)"} true;
L2:

    // $t14 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:42+9
    assume {:print "$at(7,2877,2886)"} true;
    $t14 := 0;
    assume $IsValid'u64'($t14);

    // trace_abort($t14) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:13+6
    assume {:print "$at(7,2848,2854)"} true;
    assume {:print "$track_abort(98,9):", $t14} $t14 == $t14;

    // $t3 := move($t14) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:13+6
    $t3 := $t14;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:123:13+6
    goto L6;

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:128:5+1
    assume {:print "$at(7,2977,2978)"} true;
L5:

    // return $t1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:128:5+1
    assume {:print "$at(7,2977,2978)"} true;
    $ret0 := $t1;
    return;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:128:5+1
L6:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:128:5+1
    assume {:print "$at(7,2977,2978)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun i32::as_u32 [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:167:5+53
procedure {:inline 1} $aa_i32_as_u32(_$t0: $aa_i32_I32) returns ($ret0: bv32)
{
    // declare local variables
    var $t1: bv32;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'bv32': bv32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:167:5+1
    assume {:print "$at(7,3784,3785)"} true;
    assume {:print "$track_local(98,12,0):", $t0} $t0 == $t0;

    // $t1 := get_field<0xaa::i32::I32>.bits($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:168:9+6
    assume {:print "$at(7,3825,3831)"} true;
    $t1 := $t0->$bits;

    // trace_return[0]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:168:9+6
    assume {:print "$track_return(98,12,0):", $t1} $t1 == $t1;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:169:5+1
    assume {:print "$at(7,3836,3837)"} true;
L1:

    // return $t1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:169:5+1
    assume {:print "$at(7,3836,3837)"} true;
    $ret0 := $t1;
    return;

}

// fun i32::is_neg [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:175:5+60
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
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:175:5+1
    assume {:print "$at(7,3915,3916)"} true;
    assume {:print "$track_local(98,17,0):", $t0} $t0 == $t0;

    // $t1 := i32::sign($t0) on_abort goto L2 with $t2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:176:9+7
    assume {:print "$at(7,3957,3964)"} true;
    call $t1 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,3957,3964)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(98,17):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := 1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:176:20+1
    $t3 := 1;
    assume $IsValid'u8'($t3);

    // $t4 := ==($t1, $t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:176:9+12
    $t4 := $IsEqual'u8'($t1, $t3);

    // trace_return[0]($t4) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:176:9+12
    assume {:print "$track_return(98,17,0):", $t4} $t4 == $t4;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:177:5+1
    assume {:print "$at(7,3974,3975)"} true;
L1:

    // return $t4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:177:5+1
    assume {:print "$at(7,3974,3975)"} true;
    $ret0 := $t4;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:177:5+1
L2:

    // abort($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:177:5+1
    assume {:print "$at(7,3974,3975)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun i32::lt [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:202:5+79
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
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:202:5+1
    assume {:print "$at(7,4543,4544)"} true;
    assume {:print "$track_local(98,18,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:202:5+1
    assume {:print "$track_local(98,18,1):", $t1} $t1 == $t1;

    // $t2 := i32::cmp($t0, $t1) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:203:9+15
    assume {:print "$at(7,4595,4610)"} true;
    call $t2 := $aa_i32_cmp($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(7,4595,4610)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,18):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:203:28+2
    $t4 := 0;
    assume $IsValid'u8'($t4);

    // $t5 := ==($t2, $t4) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:203:9+21
    $t5 := $IsEqual'u8'($t2, $t4);

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:203:9+21
    assume {:print "$track_return(98,18,0):", $t5} $t5 == $t5;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:204:5+1
    assume {:print "$at(7,4621,4622)"} true;
L1:

    // return $t5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:204:5+1
    assume {:print "$at(7,4621,4622)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:204:5+1
L2:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:204:5+1
    assume {:print "$at(7,4621,4622)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun i32::u32_neg [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:244:5+55
procedure {:inline 1} $aa_i32_u32_neg(_$t0: bv32) returns ($ret0: bv32)
{
    // declare local variables
    var $t1: int;
    var $t2: bv32;
    var $t0: bv32;
    var $temp_0'bv32': bv32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:244:5+1
    assume {:print "$at(7,5565,5566)"} true;
    assume {:print "$track_local(98,26,0):", $t0} $t0 == $t0;

    // $t1 := 4294967295 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:245:13+10
    assume {:print "$at(7,5604,5614)"} true;
    $t1 := 4294967295;
    assume $IsValid'u32'($t1);

    // $t2 := ^($t0, $t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:245:9+14
    call $t2 := $XorBv32($t0, $int2bv.32($t1));

    // trace_return[0]($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:245:9+14
    assume {:print "$track_return(98,26,0):", $t2} $t2 == $t2;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:246:5+1
    assume {:print "$at(7,5619,5620)"} true;
L1:

    // return $t2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i32.move:246:5+1
    assume {:print "$at(7,5619,5620)"} true;
    $ret0 := $t2;
    return;

}

// struct i128::I128 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/i128.move:15:5+60
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

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:131:5+3332
function {:inline} $aa_tick_math_$get_sqrt_price_at_negative_tick(tick: $aa_i32_I32): int {
    (var abs_tick := $aa_i32_$as_u32($aa_i32_$abs(tick)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 1bv32), 0bv32)) then (18445821805675392311) else (18446744073709551616)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 4bv32), 0bv32)) then ($shr((ratio * 18443055278223354162), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 8bv32), 0bv32)) then ($shr((ratio * 18439367220385604838), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 16bv32), 0bv32)) then ($shr((ratio * 18431993317065449817), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 32bv32), 0bv32)) then ($shr((ratio * 18417254355718160513), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 64bv32), 0bv32)) then ($shr((ratio * 18387811781193591352), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 128bv32), 0bv32)) then ($shr((ratio * 18329067761203520168), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 256bv32), 0bv32)) then ($shr((ratio * 18212142134806087854), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 512bv32), 0bv32)) then ($shr((ratio * 17980523815641551639), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 1024bv32), 0bv32)) then ($shr((ratio * 17526086738831147013), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 2048bv32), 0bv32)) then ($shr((ratio * 16651378430235024244), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 4096bv32), 0bv32)) then ($shr((ratio * 15030750278693429944), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 8192bv32), 0bv32)) then ($shr((ratio * 12247334978882834399), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 16384bv32), 0bv32)) then ($shr((ratio * 8131365268884726200), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 32768bv32), 0bv32)) then ($shr((ratio * 3584323654723342297), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 65536bv32), 0bv32)) then ($shr((ratio * 696457651847595233), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 131072bv32), 0bv32)) then ($shr((ratio * 26294789957452057), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 262144bv32), 0bv32)) then ($shr((ratio * 37481735321082), 64)) else (ratio)); ratio)))))))))))))))))))
}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:227:5+3631
function {:inline} $aa_tick_math_$get_sqrt_price_at_positive_tick(tick: $aa_i32_I32): int {
    (var abs_tick := $aa_i32_$as_u32($aa_i32_$abs(tick)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 1bv32), 0bv32)) then (18445821805675392311) else (18446744073709551616)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 4bv32), 0bv32)) then ($shr((ratio * 18443055278223354162), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 8bv32), 0bv32)) then ($shr((ratio * 18439367220385604838), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 16bv32), 0bv32)) then ($shr((ratio * 18431993317065449817), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 32bv32), 0bv32)) then ($shr((ratio * 18417254355718160513), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 64bv32), 0bv32)) then ($shr((ratio * 18387811781193591352), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 128bv32), 0bv32)) then ($shr((ratio * 18329067761203520168), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 256bv32), 0bv32)) then ($shr((ratio * 18212142134806087854), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 512bv32), 0bv32)) then ($shr((ratio * 17980523815641551639), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 1024bv32), 0bv32)) then ($shr((ratio * 17526086738831147013), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 2048bv32), 0bv32)) then ($shr((ratio * 16651378430235024244), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 4096bv32), 0bv32)) then ($shr((ratio * 15030750278693429944), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 8192bv32), 0bv32)) then ($shr((ratio * 12247334978882834399), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 16384bv32), 0bv32)) then ($shr((ratio * 8131365268884726200), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 32768bv32), 0bv32)) then ($shr((ratio * 3584323654723342297), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 65536bv32), 0bv32)) then ($shr((ratio * 696457651847595233), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 131072bv32), 0bv32)) then ($shr((ratio * 26294789957452057), 64)) else (ratio)); (var ratio := (if (!$IsEqual'bv32'($And'Bv32'(abs_tick, 262144bv32), 0bv32)) then ($shr((ratio * 37481735321082), 64)) else (ratio)); ratio)))))))))))))))))))
}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:51:5+316
function {:inline} $aa_tick_math_$get_sqrt_price_at_tick(tick: $aa_i32_I32): int {
    (if ($aa_i32_$is_neg(tick)) then ($aa_tick_math_$get_sqrt_price_at_negative_tick(tick)) else ($aa_tick_math_$get_sqrt_price_at_positive_tick(tick)))
}

// fun tick_math::get_sqrt_price_at_negative_tick [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:131:5+3332
procedure {:inline 1} $aa_tick_math_get_sqrt_price_at_negative_tick(_$t0: $aa_i32_I32) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: $aa_i32_I32;
    var $t21: int;
    var $t22: bv32;
    var $t23: int;
    var $t24: bv32;
    var $t25: bv32;
    var $t26: bool;
    var $t27: int;
    var $t28: int;
    var $t29: bv32;
    var $t30: bv32;
    var $t31: bool;
    var $t32: int;
    var $t33: int;
    var $t34: int;
    var $t35: int;
    var $t36: int;
    var $t37: int;
    var $t38: int;
    var $t39: bv32;
    var $t40: bv32;
    var $t41: bool;
    var $t42: int;
    var $t43: int;
    var $t44: int;
    var $t45: int;
    var $t46: int;
    var $t47: int;
    var $t48: int;
    var $t49: bv32;
    var $t50: bv32;
    var $t51: bool;
    var $t52: int;
    var $t53: int;
    var $t54: int;
    var $t55: int;
    var $t56: int;
    var $t57: int;
    var $t58: int;
    var $t59: bv32;
    var $t60: bv32;
    var $t61: bool;
    var $t62: int;
    var $t63: int;
    var $t64: int;
    var $t65: int;
    var $t66: int;
    var $t67: int;
    var $t68: int;
    var $t69: bv32;
    var $t70: bv32;
    var $t71: bool;
    var $t72: int;
    var $t73: int;
    var $t74: int;
    var $t75: int;
    var $t76: int;
    var $t77: int;
    var $t78: int;
    var $t79: bv32;
    var $t80: bv32;
    var $t81: bool;
    var $t82: int;
    var $t83: int;
    var $t84: int;
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
    var $t96: int;
    var $t97: int;
    var $t98: int;
    var $t99: bv32;
    var $t100: bv32;
    var $t101: bool;
    var $t102: int;
    var $t103: int;
    var $t104: int;
    var $t105: int;
    var $t106: int;
    var $t107: int;
    var $t108: int;
    var $t109: bv32;
    var $t110: bv32;
    var $t111: bool;
    var $t112: int;
    var $t113: int;
    var $t114: int;
    var $t115: int;
    var $t116: int;
    var $t117: int;
    var $t118: int;
    var $t119: bv32;
    var $t120: bv32;
    var $t121: bool;
    var $t122: int;
    var $t123: int;
    var $t124: int;
    var $t125: int;
    var $t126: int;
    var $t127: int;
    var $t128: int;
    var $t129: bv32;
    var $t130: bv32;
    var $t131: bool;
    var $t132: int;
    var $t133: int;
    var $t134: int;
    var $t135: int;
    var $t136: int;
    var $t137: int;
    var $t138: int;
    var $t139: bv32;
    var $t140: bv32;
    var $t141: bool;
    var $t142: int;
    var $t143: int;
    var $t144: int;
    var $t145: int;
    var $t146: int;
    var $t147: int;
    var $t148: int;
    var $t149: bv32;
    var $t150: bv32;
    var $t151: bool;
    var $t152: int;
    var $t153: int;
    var $t154: int;
    var $t155: int;
    var $t156: int;
    var $t157: int;
    var $t158: int;
    var $t159: bv32;
    var $t160: bv32;
    var $t161: bool;
    var $t162: int;
    var $t163: int;
    var $t164: int;
    var $t165: int;
    var $t166: int;
    var $t167: int;
    var $t168: int;
    var $t169: bv32;
    var $t170: bv32;
    var $t171: bool;
    var $t172: int;
    var $t173: int;
    var $t174: int;
    var $t175: int;
    var $t176: int;
    var $t177: int;
    var $t178: int;
    var $t179: bv32;
    var $t180: bv32;
    var $t181: bool;
    var $t182: int;
    var $t183: int;
    var $t184: int;
    var $t185: int;
    var $t186: int;
    var $t187: int;
    var $t188: int;
    var $t189: bv32;
    var $t190: bv32;
    var $t191: bool;
    var $t192: int;
    var $t193: int;
    var $t194: int;
    var $t195: int;
    var $t196: int;
    var $t197: int;
    var $t198: int;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'u128': int;
    var $temp_0'bv32': bv32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[tick]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:131:5+1
    assume {:print "$at(13,3984,3985)"} true;
    assume {:print "$track_local(101,2,0):", $t0} $t0 == $t0;

    // $t20 := i32::abs($t0) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:132:36+14
    assume {:print "$at(13,4079,4093)"} true;
    call $t20 := $aa_i32_abs($t0);
    if ($abort_flag) {
        assume {:print "$at(13,4079,4093)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t22 := i32::as_u32($t20) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:132:24+27
    call $t22 := $aa_i32_as_u32($t20);
    if ($abort_flag) {
        assume {:print "$at(13,4067,4094)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // trace_local[abs_tick]($t22) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:132:24+27
    assume {:print "$track_local(101,2,1):", $t22} $t22 == $t22;

    // $t23 := 1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:133:36+3
    assume {:print "$at(13,4131,4134)"} true;
    $t23 := 1;
    assume $IsValid'u32'($t23);

    // $t24 := &($t22, $t23) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:133:25+14
    call $t24 := $AndBv32($t22, $int2bv.32($t23));

    // $t25 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:133:43+1
    $t25 := 0bv32;
    assume $IsValid'bv32'($t25);

    // $t26 := !=($t24, $t25) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:133:25+19
    $t26 := !$IsEqual'bv32'($t24, $t25);

    // if ($t26) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:133:21+127
    if ($t26) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:134:13+24
    assume {:print "$at(13,4155,4179)"} true;
L1:

    // $t27 := 18445821805675392311 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:134:13+24
    assume {:print "$at(13,4155,4179)"} true;
    $t27 := 18445821805675392311;
    assume $IsValid'u128'($t27);

    // $t2 := $t27 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:134:13+24
    $t2 := $t27;

    // trace_local[ratio]($t27) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:134:13+24
    assume {:print "$track_local(101,2,2):", $t27} $t27 == $t27;

    // label L53 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:138:25+8
    assume {:print "$at(13,4269,4277)"} true;
L53:

    // $t28 := 4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:138:36+3
    assume {:print "$at(13,4280,4283)"} true;
    $t28 := 4;
    assume $IsValid'u32'($t28);

    // $t29 := &($t22, $t28) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:138:25+14
    call $t29 := $AndBv32($t22, $int2bv.32($t28));

    // $t30 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:138:43+1
    $t30 := 0bv32;
    assume $IsValid'bv32'($t30);

    // $t31 := !=($t29, $t30) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:138:25+19
    $t31 := !$IsEqual'bv32'($t29, $t30);

    // if ($t31) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:138:21+156
    if ($t31) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:139:15+15
    assume {:print "$at(13,4306,4321)"} true;
L3:

    // $t32 := (u256)($t2) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:139:15+15
    assume {:print "$at(13,4306,4321)"} true;
    call $t32 := $CastU256($t2);
    if ($abort_flag) {
        assume {:print "$at(13,4306,4321)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t33 := 18443055278223354162 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:139:33+34
    $t33 := 18443055278223354162;
    assume $IsValid'u256'($t33);

    // $t34 := *($t32, $t33) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:139:14+54
    call $t34 := $MulU256($t32, $t33);
    if ($abort_flag) {
        assume {:print "$at(13,4305,4359)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t35 := (u128)($t34) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:139:13+64
    call $t35 := $CastU128($t34);
    if ($abort_flag) {
        assume {:print "$at(13,4304,4368)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t36 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:139:81+4
    $t36 := 64;
    assume $IsValid'u8'($t36);

    // $t37 := >>($t35, $t36) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:139:13+72
    call $t37 := $ShrU128($t35, $t36);
    if ($abort_flag) {
        assume {:print "$at(13,4304,4376)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t3 := $t37 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:139:13+72
    $t3 := $t37;

    // trace_local[$t16]($t37) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:139:13+72
    assume {:print "$track_local(101,2,3):", $t37} $t37 == $t37;

    // label L52 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:143:25+8
    assume {:print "$at(13,4447,4455)"} true;
L52:

    // $t38 := 8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:143:36+3
    assume {:print "$at(13,4458,4461)"} true;
    $t38 := 8;
    assume $IsValid'u32'($t38);

    // $t39 := &($t22, $t38) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:143:25+14
    call $t39 := $AndBv32($t22, $int2bv.32($t38));

    // $t40 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:143:43+1
    $t40 := 0bv32;
    assume $IsValid'bv32'($t40);

    // $t41 := !=($t39, $t40) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:143:25+19
    $t41 := !$IsEqual'bv32'($t39, $t40);

    // if ($t41) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:143:21+156
    if ($t41) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:144:15+15
    assume {:print "$at(13,4484,4499)"} true;
L5:

    // $t42 := (u256)($t3) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:144:15+15
    assume {:print "$at(13,4484,4499)"} true;
    call $t42 := $CastU256($t3);
    if ($abort_flag) {
        assume {:print "$at(13,4484,4499)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t43 := 18439367220385604838 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:144:33+34
    $t43 := 18439367220385604838;
    assume $IsValid'u256'($t43);

    // $t44 := *($t42, $t43) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:144:14+54
    call $t44 := $MulU256($t42, $t43);
    if ($abort_flag) {
        assume {:print "$at(13,4483,4537)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t45 := (u128)($t44) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:144:13+64
    call $t45 := $CastU128($t44);
    if ($abort_flag) {
        assume {:print "$at(13,4482,4546)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t46 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:144:81+4
    $t46 := 64;
    assume $IsValid'u8'($t46);

    // $t47 := >>($t45, $t46) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:144:13+72
    call $t47 := $ShrU128($t45, $t46);
    if ($abort_flag) {
        assume {:print "$at(13,4482,4554)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t4 := $t47 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:144:13+72
    $t4 := $t47;

    // trace_local[$t27]($t47) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:144:13+72
    assume {:print "$track_local(101,2,4):", $t47} $t47 == $t47;

    // label L51 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:148:26+8
    assume {:print "$at(13,4626,4634)"} true;
L51:

    // $t48 := 16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:148:37+4
    assume {:print "$at(13,4637,4641)"} true;
    $t48 := 16;
    assume $IsValid'u32'($t48);

    // $t49 := &($t22, $t48) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:148:26+15
    call $t49 := $AndBv32($t22, $int2bv.32($t48));

    // $t50 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:148:45+1
    $t50 := 0bv32;
    assume $IsValid'bv32'($t50);

    // $t51 := !=($t49, $t50) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:148:26+20
    $t51 := !$IsEqual'bv32'($t49, $t50);

    // if ($t51) goto L7 else goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:148:22+157
    if ($t51) { goto L7; } else { goto L6; }

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:149:15+15
    assume {:print "$at(13,4664,4679)"} true;
L7:

    // $t52 := (u256)($t4) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:149:15+15
    assume {:print "$at(13,4664,4679)"} true;
    call $t52 := $CastU256($t4);
    if ($abort_flag) {
        assume {:print "$at(13,4664,4679)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t53 := 18431993317065449817 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:149:33+34
    $t53 := 18431993317065449817;
    assume $IsValid'u256'($t53);

    // $t54 := *($t52, $t53) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:149:14+54
    call $t54 := $MulU256($t52, $t53);
    if ($abort_flag) {
        assume {:print "$at(13,4663,4717)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t55 := (u128)($t54) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:149:13+64
    call $t55 := $CastU128($t54);
    if ($abort_flag) {
        assume {:print "$at(13,4662,4726)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t56 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:149:81+4
    $t56 := 64;
    assume $IsValid'u8'($t56);

    // $t57 := >>($t55, $t56) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:149:13+72
    call $t57 := $ShrU128($t55, $t56);
    if ($abort_flag) {
        assume {:print "$at(13,4662,4734)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t5 := $t57 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:149:13+72
    $t5 := $t57;

    // trace_local[$t38]($t57) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:149:13+72
    assume {:print "$track_local(101,2,5):", $t57} $t57 == $t57;

    // label L50 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:153:25+8
    assume {:print "$at(13,4805,4813)"} true;
L50:

    // $t58 := 32 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:153:36+4
    assume {:print "$at(13,4816,4820)"} true;
    $t58 := 32;
    assume $IsValid'u32'($t58);

    // $t59 := &($t22, $t58) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:153:25+15
    call $t59 := $AndBv32($t22, $int2bv.32($t58));

    // $t60 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:153:44+1
    $t60 := 0bv32;
    assume $IsValid'bv32'($t60);

    // $t61 := !=($t59, $t60) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:153:25+20
    $t61 := !$IsEqual'bv32'($t59, $t60);

    // if ($t61) goto L9 else goto L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:153:21+158
    if ($t61) { goto L9; } else { goto L8; }

    // label L9 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:154:16+15
    assume {:print "$at(13,4844,4859)"} true;
L9:

    // $t62 := (u256)($t5) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:154:16+15
    assume {:print "$at(13,4844,4859)"} true;
    call $t62 := $CastU256($t5);
    if ($abort_flag) {
        assume {:print "$at(13,4844,4859)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t63 := 18417254355718160513 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:154:34+34
    $t63 := 18417254355718160513;
    assume $IsValid'u256'($t63);

    // $t64 := *($t62, $t63) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:154:15+54
    call $t64 := $MulU256($t62, $t63);
    if ($abort_flag) {
        assume {:print "$at(13,4843,4897)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t65 := (u128)($t64) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:154:14+64
    call $t65 := $CastU128($t64);
    if ($abort_flag) {
        assume {:print "$at(13,4842,4906)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t66 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:154:82+4
    $t66 := 64;
    assume $IsValid'u8'($t66);

    // $t67 := >>($t65, $t66) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:154:14+72
    call $t67 := $ShrU128($t65, $t66);
    if ($abort_flag) {
        assume {:print "$at(13,4842,4914)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t6 := $t67 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:154:14+72
    $t6 := $t67;

    // trace_local[$t49]($t67) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:154:14+72
    assume {:print "$track_local(101,2,6):", $t67} $t67 == $t67;

    // label L49 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:158:25+8
    assume {:print "$at(13,4985,4993)"} true;
L49:

    // $t68 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:158:36+4
    assume {:print "$at(13,4996,5000)"} true;
    $t68 := 64;
    assume $IsValid'u32'($t68);

    // $t69 := &($t22, $t68) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:158:25+15
    call $t69 := $AndBv32($t22, $int2bv.32($t68));

    // $t70 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:158:44+1
    $t70 := 0bv32;
    assume $IsValid'bv32'($t70);

    // $t71 := !=($t69, $t70) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:158:25+20
    $t71 := !$IsEqual'bv32'($t69, $t70);

    // if ($t71) goto L11 else goto L10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:158:21+157
    if ($t71) { goto L11; } else { goto L10; }

    // label L11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:159:15+15
    assume {:print "$at(13,5023,5038)"} true;
L11:

    // $t72 := (u256)($t6) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:159:15+15
    assume {:print "$at(13,5023,5038)"} true;
    call $t72 := $CastU256($t6);
    if ($abort_flag) {
        assume {:print "$at(13,5023,5038)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t73 := 18387811781193591352 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:159:33+34
    $t73 := 18387811781193591352;
    assume $IsValid'u256'($t73);

    // $t74 := *($t72, $t73) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:159:14+54
    call $t74 := $MulU256($t72, $t73);
    if ($abort_flag) {
        assume {:print "$at(13,5022,5076)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t75 := (u128)($t74) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:159:13+64
    call $t75 := $CastU128($t74);
    if ($abort_flag) {
        assume {:print "$at(13,5021,5085)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t76 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:159:81+4
    $t76 := 64;
    assume $IsValid'u8'($t76);

    // $t77 := >>($t75, $t76) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:159:13+72
    call $t77 := $ShrU128($t75, $t76);
    if ($abort_flag) {
        assume {:print "$at(13,5021,5093)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t7 := $t77 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:159:13+72
    $t7 := $t77;

    // trace_local[$t60]($t77) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:159:13+72
    assume {:print "$track_local(101,2,7):", $t77} $t77 == $t77;

    // label L48 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:163:25+8
    assume {:print "$at(13,5164,5172)"} true;
L48:

    // $t78 := 128 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:163:36+4
    assume {:print "$at(13,5175,5179)"} true;
    $t78 := 128;
    assume $IsValid'u32'($t78);

    // $t79 := &($t22, $t78) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:163:25+15
    call $t79 := $AndBv32($t22, $int2bv.32($t78));

    // $t80 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:163:44+1
    $t80 := 0bv32;
    assume $IsValid'bv32'($t80);

    // $t81 := !=($t79, $t80) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:163:25+20
    $t81 := !$IsEqual'bv32'($t79, $t80);

    // if ($t81) goto L13 else goto L12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:163:21+157
    if ($t81) { goto L13; } else { goto L12; }

    // label L13 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:164:15+15
    assume {:print "$at(13,5202,5217)"} true;
L13:

    // $t82 := (u256)($t7) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:164:15+15
    assume {:print "$at(13,5202,5217)"} true;
    call $t82 := $CastU256($t7);
    if ($abort_flag) {
        assume {:print "$at(13,5202,5217)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t83 := 18329067761203520168 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:164:33+34
    $t83 := 18329067761203520168;
    assume $IsValid'u256'($t83);

    // $t84 := *($t82, $t83) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:164:14+54
    call $t84 := $MulU256($t82, $t83);
    if ($abort_flag) {
        assume {:print "$at(13,5201,5255)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t85 := (u128)($t84) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:164:13+64
    call $t85 := $CastU128($t84);
    if ($abort_flag) {
        assume {:print "$at(13,5200,5264)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t86 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:164:81+4
    $t86 := 64;
    assume $IsValid'u8'($t86);

    // $t87 := >>($t85, $t86) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:164:13+72
    call $t87 := $ShrU128($t85, $t86);
    if ($abort_flag) {
        assume {:print "$at(13,5200,5272)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t8 := $t87 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:164:13+72
    $t8 := $t87;

    // trace_local[$t71]($t87) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:164:13+72
    assume {:print "$track_local(101,2,8):", $t87} $t87 == $t87;

    // label L47 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:168:25+8
    assume {:print "$at(13,5343,5351)"} true;
L47:

    // $t88 := 256 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:168:36+5
    assume {:print "$at(13,5354,5359)"} true;
    $t88 := 256;
    assume $IsValid'u32'($t88);

    // $t89 := &($t22, $t88) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:168:25+16
    call $t89 := $AndBv32($t22, $int2bv.32($t88));

    // $t90 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:168:45+1
    $t90 := 0bv32;
    assume $IsValid'bv32'($t90);

    // $t91 := !=($t89, $t90) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:168:25+21
    $t91 := !$IsEqual'bv32'($t89, $t90);

    // if ($t91) goto L15 else goto L14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:168:21+158
    if ($t91) { goto L15; } else { goto L14; }

    // label L15 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:169:15+15
    assume {:print "$at(13,5382,5397)"} true;
L15:

    // $t92 := (u256)($t8) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:169:15+15
    assume {:print "$at(13,5382,5397)"} true;
    call $t92 := $CastU256($t8);
    if ($abort_flag) {
        assume {:print "$at(13,5382,5397)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t93 := 18212142134806087854 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:169:33+34
    $t93 := 18212142134806087854;
    assume $IsValid'u256'($t93);

    // $t94 := *($t92, $t93) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:169:14+54
    call $t94 := $MulU256($t92, $t93);
    if ($abort_flag) {
        assume {:print "$at(13,5381,5435)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t95 := (u128)($t94) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:169:13+64
    call $t95 := $CastU128($t94);
    if ($abort_flag) {
        assume {:print "$at(13,5380,5444)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t96 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:169:81+4
    $t96 := 64;
    assume $IsValid'u8'($t96);

    // $t97 := >>($t95, $t96) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:169:13+72
    call $t97 := $ShrU128($t95, $t96);
    if ($abort_flag) {
        assume {:print "$at(13,5380,5452)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t9 := $t97 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:169:13+72
    $t9 := $t97;

    // trace_local[$t82]($t97) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:169:13+72
    assume {:print "$track_local(101,2,9):", $t97} $t97 == $t97;

    // label L46 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:173:25+8
    assume {:print "$at(13,5523,5531)"} true;
L46:

    // $t98 := 512 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:173:36+5
    assume {:print "$at(13,5534,5539)"} true;
    $t98 := 512;
    assume $IsValid'u32'($t98);

    // $t99 := &($t22, $t98) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:173:25+16
    call $t99 := $AndBv32($t22, $int2bv.32($t98));

    // $t100 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:173:45+1
    $t100 := 0bv32;
    assume $IsValid'bv32'($t100);

    // $t101 := !=($t99, $t100) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:173:25+21
    $t101 := !$IsEqual'bv32'($t99, $t100);

    // if ($t101) goto L17 else goto L16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:173:21+158
    if ($t101) { goto L17; } else { goto L16; }

    // label L17 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:174:15+15
    assume {:print "$at(13,5562,5577)"} true;
L17:

    // $t102 := (u256)($t9) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:174:15+15
    assume {:print "$at(13,5562,5577)"} true;
    call $t102 := $CastU256($t9);
    if ($abort_flag) {
        assume {:print "$at(13,5562,5577)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t103 := 17980523815641551639 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:174:33+34
    $t103 := 17980523815641551639;
    assume $IsValid'u256'($t103);

    // $t104 := *($t102, $t103) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:174:14+54
    call $t104 := $MulU256($t102, $t103);
    if ($abort_flag) {
        assume {:print "$at(13,5561,5615)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t105 := (u128)($t104) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:174:13+64
    call $t105 := $CastU128($t104);
    if ($abort_flag) {
        assume {:print "$at(13,5560,5624)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t106 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:174:81+4
    $t106 := 64;
    assume $IsValid'u8'($t106);

    // $t107 := >>($t105, $t106) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:174:13+72
    call $t107 := $ShrU128($t105, $t106);
    if ($abort_flag) {
        assume {:print "$at(13,5560,5632)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t10 := $t107 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:174:13+72
    $t10 := $t107;

    // trace_local[$t93]($t107) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:174:13+72
    assume {:print "$track_local(101,2,10):", $t107} $t107 == $t107;

    // label L45 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:178:25+8
    assume {:print "$at(13,5703,5711)"} true;
L45:

    // $t108 := 1024 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:178:36+5
    assume {:print "$at(13,5714,5719)"} true;
    $t108 := 1024;
    assume $IsValid'u32'($t108);

    // $t109 := &($t22, $t108) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:178:25+16
    call $t109 := $AndBv32($t22, $int2bv.32($t108));

    // $t110 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:178:45+1
    $t110 := 0bv32;
    assume $IsValid'bv32'($t110);

    // $t111 := !=($t109, $t110) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:178:25+21
    $t111 := !$IsEqual'bv32'($t109, $t110);

    // if ($t111) goto L19 else goto L18 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:178:21+158
    if ($t111) { goto L19; } else { goto L18; }

    // label L19 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:179:15+15
    assume {:print "$at(13,5742,5757)"} true;
L19:

    // $t112 := (u256)($t10) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:179:15+15
    assume {:print "$at(13,5742,5757)"} true;
    call $t112 := $CastU256($t10);
    if ($abort_flag) {
        assume {:print "$at(13,5742,5757)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t113 := 17526086738831147013 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:179:33+34
    $t113 := 17526086738831147013;
    assume $IsValid'u256'($t113);

    // $t114 := *($t112, $t113) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:179:14+54
    call $t114 := $MulU256($t112, $t113);
    if ($abort_flag) {
        assume {:print "$at(13,5741,5795)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t115 := (u128)($t114) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:179:13+64
    call $t115 := $CastU128($t114);
    if ($abort_flag) {
        assume {:print "$at(13,5740,5804)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t116 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:179:81+4
    $t116 := 64;
    assume $IsValid'u8'($t116);

    // $t117 := >>($t115, $t116) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:179:13+72
    call $t117 := $ShrU128($t115, $t116);
    if ($abort_flag) {
        assume {:print "$at(13,5740,5812)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t11 := $t117 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:179:13+72
    $t11 := $t117;

    // trace_local[$t104]($t117) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:179:13+72
    assume {:print "$track_local(101,2,11):", $t117} $t117 == $t117;

    // label L44 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:183:25+8
    assume {:print "$at(13,5883,5891)"} true;
L44:

    // $t118 := 2048 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:183:36+5
    assume {:print "$at(13,5894,5899)"} true;
    $t118 := 2048;
    assume $IsValid'u32'($t118);

    // $t119 := &($t22, $t118) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:183:25+16
    call $t119 := $AndBv32($t22, $int2bv.32($t118));

    // $t120 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:183:45+1
    $t120 := 0bv32;
    assume $IsValid'bv32'($t120);

    // $t121 := !=($t119, $t120) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:183:25+21
    $t121 := !$IsEqual'bv32'($t119, $t120);

    // if ($t121) goto L21 else goto L20 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:183:21+158
    if ($t121) { goto L21; } else { goto L20; }

    // label L21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:184:15+15
    assume {:print "$at(13,5922,5937)"} true;
L21:

    // $t122 := (u256)($t11) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:184:15+15
    assume {:print "$at(13,5922,5937)"} true;
    call $t122 := $CastU256($t11);
    if ($abort_flag) {
        assume {:print "$at(13,5922,5937)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t123 := 16651378430235024244 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:184:33+34
    $t123 := 16651378430235024244;
    assume $IsValid'u256'($t123);

    // $t124 := *($t122, $t123) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:184:14+54
    call $t124 := $MulU256($t122, $t123);
    if ($abort_flag) {
        assume {:print "$at(13,5921,5975)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t125 := (u128)($t124) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:184:13+64
    call $t125 := $CastU128($t124);
    if ($abort_flag) {
        assume {:print "$at(13,5920,5984)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t126 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:184:81+4
    $t126 := 64;
    assume $IsValid'u8'($t126);

    // $t127 := >>($t125, $t126) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:184:13+72
    call $t127 := $ShrU128($t125, $t126);
    if ($abort_flag) {
        assume {:print "$at(13,5920,5992)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t12 := $t127 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:184:13+72
    $t12 := $t127;

    // trace_local[$t115]($t127) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:184:13+72
    assume {:print "$track_local(101,2,12):", $t127} $t127 == $t127;

    // label L43 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:188:25+8
    assume {:print "$at(13,6063,6071)"} true;
L43:

    // $t128 := 4096 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:188:36+6
    assume {:print "$at(13,6074,6080)"} true;
    $t128 := 4096;
    assume $IsValid'u32'($t128);

    // $t129 := &($t22, $t128) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:188:25+17
    call $t129 := $AndBv32($t22, $int2bv.32($t128));

    // $t130 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:188:46+1
    $t130 := 0bv32;
    assume $IsValid'bv32'($t130);

    // $t131 := !=($t129, $t130) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:188:25+22
    $t131 := !$IsEqual'bv32'($t129, $t130);

    // if ($t131) goto L23 else goto L22 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:188:21+159
    if ($t131) { goto L23; } else { goto L22; }

    // label L23 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:189:15+15
    assume {:print "$at(13,6103,6118)"} true;
L23:

    // $t132 := (u256)($t12) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:189:15+15
    assume {:print "$at(13,6103,6118)"} true;
    call $t132 := $CastU256($t12);
    if ($abort_flag) {
        assume {:print "$at(13,6103,6118)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t133 := 15030750278693429944 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:189:33+34
    $t133 := 15030750278693429944;
    assume $IsValid'u256'($t133);

    // $t134 := *($t132, $t133) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:189:14+54
    call $t134 := $MulU256($t132, $t133);
    if ($abort_flag) {
        assume {:print "$at(13,6102,6156)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t135 := (u128)($t134) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:189:13+64
    call $t135 := $CastU128($t134);
    if ($abort_flag) {
        assume {:print "$at(13,6101,6165)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t136 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:189:81+4
    $t136 := 64;
    assume $IsValid'u8'($t136);

    // $t137 := >>($t135, $t136) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:189:13+72
    call $t137 := $ShrU128($t135, $t136);
    if ($abort_flag) {
        assume {:print "$at(13,6101,6173)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t13 := $t137 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:189:13+72
    $t13 := $t137;

    // trace_local[$t126]($t137) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:189:13+72
    assume {:print "$track_local(101,2,13):", $t137} $t137 == $t137;

    // label L42 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:193:25+8
    assume {:print "$at(13,6244,6252)"} true;
L42:

    // $t138 := 8192 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:193:36+6
    assume {:print "$at(13,6255,6261)"} true;
    $t138 := 8192;
    assume $IsValid'u32'($t138);

    // $t139 := &($t22, $t138) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:193:25+17
    call $t139 := $AndBv32($t22, $int2bv.32($t138));

    // $t140 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:193:46+1
    $t140 := 0bv32;
    assume $IsValid'bv32'($t140);

    // $t141 := !=($t139, $t140) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:193:25+22
    $t141 := !$IsEqual'bv32'($t139, $t140);

    // if ($t141) goto L25 else goto L24 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:193:21+159
    if ($t141) { goto L25; } else { goto L24; }

    // label L25 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:194:15+15
    assume {:print "$at(13,6284,6299)"} true;
L25:

    // $t142 := (u256)($t13) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:194:15+15
    assume {:print "$at(13,6284,6299)"} true;
    call $t142 := $CastU256($t13);
    if ($abort_flag) {
        assume {:print "$at(13,6284,6299)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t143 := 12247334978882834399 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:194:33+34
    $t143 := 12247334978882834399;
    assume $IsValid'u256'($t143);

    // $t144 := *($t142, $t143) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:194:14+54
    call $t144 := $MulU256($t142, $t143);
    if ($abort_flag) {
        assume {:print "$at(13,6283,6337)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t145 := (u128)($t144) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:194:13+64
    call $t145 := $CastU128($t144);
    if ($abort_flag) {
        assume {:print "$at(13,6282,6346)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t146 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:194:81+4
    $t146 := 64;
    assume $IsValid'u8'($t146);

    // $t147 := >>($t145, $t146) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:194:13+72
    call $t147 := $ShrU128($t145, $t146);
    if ($abort_flag) {
        assume {:print "$at(13,6282,6354)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t14 := $t147 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:194:13+72
    $t14 := $t147;

    // trace_local[$t137]($t147) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:194:13+72
    assume {:print "$track_local(101,2,14):", $t147} $t147 == $t147;

    // label L41 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:198:25+8
    assume {:print "$at(13,6425,6433)"} true;
L41:

    // $t148 := 16384 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:198:36+6
    assume {:print "$at(13,6436,6442)"} true;
    $t148 := 16384;
    assume $IsValid'u32'($t148);

    // $t149 := &($t22, $t148) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:198:25+17
    call $t149 := $AndBv32($t22, $int2bv.32($t148));

    // $t150 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:198:46+1
    $t150 := 0bv32;
    assume $IsValid'bv32'($t150);

    // $t151 := !=($t149, $t150) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:198:25+22
    $t151 := !$IsEqual'bv32'($t149, $t150);

    // if ($t151) goto L27 else goto L26 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:198:21+158
    if ($t151) { goto L27; } else { goto L26; }

    // label L27 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:199:15+15
    assume {:print "$at(13,6465,6480)"} true;
L27:

    // $t152 := (u256)($t14) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:199:15+15
    assume {:print "$at(13,6465,6480)"} true;
    call $t152 := $CastU256($t14);
    if ($abort_flag) {
        assume {:print "$at(13,6465,6480)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t153 := 8131365268884726200 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:199:33+33
    $t153 := 8131365268884726200;
    assume $IsValid'u256'($t153);

    // $t154 := *($t152, $t153) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:199:14+53
    call $t154 := $MulU256($t152, $t153);
    if ($abort_flag) {
        assume {:print "$at(13,6464,6517)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t155 := (u128)($t154) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:199:13+63
    call $t155 := $CastU128($t154);
    if ($abort_flag) {
        assume {:print "$at(13,6463,6526)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t156 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:199:80+4
    $t156 := 64;
    assume $IsValid'u8'($t156);

    // $t157 := >>($t155, $t156) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:199:13+71
    call $t157 := $ShrU128($t155, $t156);
    if ($abort_flag) {
        assume {:print "$at(13,6463,6534)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t15 := $t157 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:199:13+71
    $t15 := $t157;

    // trace_local[$t148]($t157) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:199:13+71
    assume {:print "$track_local(101,2,15):", $t157} $t157 == $t157;

    // label L40 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:203:25+8
    assume {:print "$at(13,6605,6613)"} true;
L40:

    // $t158 := 32768 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:203:36+6
    assume {:print "$at(13,6616,6622)"} true;
    $t158 := 32768;
    assume $IsValid'u32'($t158);

    // $t159 := &($t22, $t158) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:203:25+17
    call $t159 := $AndBv32($t22, $int2bv.32($t158));

    // $t160 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:203:46+1
    $t160 := 0bv32;
    assume $IsValid'bv32'($t160);

    // $t161 := !=($t159, $t160) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:203:25+22
    $t161 := !$IsEqual'bv32'($t159, $t160);

    // if ($t161) goto L29 else goto L28 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:203:21+158
    if ($t161) { goto L29; } else { goto L28; }

    // label L29 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:204:15+15
    assume {:print "$at(13,6645,6660)"} true;
L29:

    // $t162 := (u256)($t15) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:204:15+15
    assume {:print "$at(13,6645,6660)"} true;
    call $t162 := $CastU256($t15);
    if ($abort_flag) {
        assume {:print "$at(13,6645,6660)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t163 := 3584323654723342297 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:204:33+33
    $t163 := 3584323654723342297;
    assume $IsValid'u256'($t163);

    // $t164 := *($t162, $t163) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:204:14+53
    call $t164 := $MulU256($t162, $t163);
    if ($abort_flag) {
        assume {:print "$at(13,6644,6697)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t165 := (u128)($t164) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:204:13+63
    call $t165 := $CastU128($t164);
    if ($abort_flag) {
        assume {:print "$at(13,6643,6706)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t166 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:204:80+4
    $t166 := 64;
    assume $IsValid'u8'($t166);

    // $t167 := >>($t165, $t166) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:204:13+71
    call $t167 := $ShrU128($t165, $t166);
    if ($abort_flag) {
        assume {:print "$at(13,6643,6714)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t16 := $t167 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:204:13+71
    $t16 := $t167;

    // trace_local[$t159]($t167) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:204:13+71
    assume {:print "$track_local(101,2,16):", $t167} $t167 == $t167;

    // label L39 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:208:25+8
    assume {:print "$at(13,6785,6793)"} true;
L39:

    // $t168 := 65536 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:208:36+7
    assume {:print "$at(13,6796,6803)"} true;
    $t168 := 65536;
    assume $IsValid'u32'($t168);

    // $t169 := &($t22, $t168) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:208:25+18
    call $t169 := $AndBv32($t22, $int2bv.32($t168));

    // $t170 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:208:47+1
    $t170 := 0bv32;
    assume $IsValid'bv32'($t170);

    // $t171 := !=($t169, $t170) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:208:25+23
    $t171 := !$IsEqual'bv32'($t169, $t170);

    // if ($t171) goto L31 else goto L30 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:208:21+158
    if ($t171) { goto L31; } else { goto L30; }

    // label L31 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:209:15+15
    assume {:print "$at(13,6826,6841)"} true;
L31:

    // $t172 := (u256)($t16) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:209:15+15
    assume {:print "$at(13,6826,6841)"} true;
    call $t172 := $CastU256($t16);
    if ($abort_flag) {
        assume {:print "$at(13,6826,6841)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t173 := 696457651847595233 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:209:33+32
    $t173 := 696457651847595233;
    assume $IsValid'u256'($t173);

    // $t174 := *($t172, $t173) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:209:14+52
    call $t174 := $MulU256($t172, $t173);
    if ($abort_flag) {
        assume {:print "$at(13,6825,6877)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t175 := (u128)($t174) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:209:13+62
    call $t175 := $CastU128($t174);
    if ($abort_flag) {
        assume {:print "$at(13,6824,6886)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t176 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:209:79+4
    $t176 := 64;
    assume $IsValid'u8'($t176);

    // $t177 := >>($t175, $t176) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:209:13+70
    call $t177 := $ShrU128($t175, $t176);
    if ($abort_flag) {
        assume {:print "$at(13,6824,6894)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t17 := $t177 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:209:13+70
    $t17 := $t177;

    // trace_local[$t170]($t177) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:209:13+70
    assume {:print "$track_local(101,2,17):", $t177} $t177 == $t177;

    // label L38 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:213:25+8
    assume {:print "$at(13,6965,6973)"} true;
L38:

    // $t178 := 131072 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:213:36+7
    assume {:print "$at(13,6976,6983)"} true;
    $t178 := 131072;
    assume $IsValid'u32'($t178);

    // $t179 := &($t22, $t178) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:213:25+18
    call $t179 := $AndBv32($t22, $int2bv.32($t178));

    // $t180 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:213:47+1
    $t180 := 0bv32;
    assume $IsValid'bv32'($t180);

    // $t181 := !=($t179, $t180) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:213:25+23
    $t181 := !$IsEqual'bv32'($t179, $t180);

    // if ($t181) goto L33 else goto L32 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:213:21+157
    if ($t181) { goto L33; } else { goto L32; }

    // label L33 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:214:15+15
    assume {:print "$at(13,7006,7021)"} true;
L33:

    // $t182 := (u256)($t17) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:214:15+15
    assume {:print "$at(13,7006,7021)"} true;
    call $t182 := $CastU256($t17);
    if ($abort_flag) {
        assume {:print "$at(13,7006,7021)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t183 := 26294789957452057 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:214:33+31
    $t183 := 26294789957452057;
    assume $IsValid'u256'($t183);

    // $t184 := *($t182, $t183) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:214:14+51
    call $t184 := $MulU256($t182, $t183);
    if ($abort_flag) {
        assume {:print "$at(13,7005,7056)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t185 := (u128)($t184) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:214:13+61
    call $t185 := $CastU128($t184);
    if ($abort_flag) {
        assume {:print "$at(13,7004,7065)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t186 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:214:78+4
    $t186 := 64;
    assume $IsValid'u8'($t186);

    // $t187 := >>($t185, $t186) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:214:13+69
    call $t187 := $ShrU128($t185, $t186);
    if ($abort_flag) {
        assume {:print "$at(13,7004,7073)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t18 := $t187 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:214:13+69
    $t18 := $t187;

    // trace_local[$t181]($t187) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:214:13+69
    assume {:print "$track_local(101,2,18):", $t187} $t187 == $t187;

    // label L37 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:218:25+8
    assume {:print "$at(13,7144,7152)"} true;
L37:

    // $t188 := 262144 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:218:36+7
    assume {:print "$at(13,7155,7162)"} true;
    $t188 := 262144;
    assume $IsValid'u32'($t188);

    // $t189 := &($t22, $t188) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:218:25+18
    call $t189 := $AndBv32($t22, $int2bv.32($t188));

    // $t190 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:218:47+1
    $t190 := 0bv32;
    assume $IsValid'bv32'($t190);

    // $t191 := !=($t189, $t190) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:218:25+23
    $t191 := !$IsEqual'bv32'($t189, $t190);

    // if ($t191) goto L35 else goto L34 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:218:21+154
    if ($t191) { goto L35; } else { goto L34; }

    // label L35 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:219:15+15
    assume {:print "$at(13,7185,7200)"} true;
L35:

    // $t192 := (u256)($t18) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:219:15+15
    assume {:print "$at(13,7185,7200)"} true;
    call $t192 := $CastU256($t18);
    if ($abort_flag) {
        assume {:print "$at(13,7185,7200)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t193 := 37481735321082 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:219:33+28
    $t193 := 37481735321082;
    assume $IsValid'u256'($t193);

    // $t194 := *($t192, $t193) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:219:14+48
    call $t194 := $MulU256($t192, $t193);
    if ($abort_flag) {
        assume {:print "$at(13,7184,7232)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t195 := (u128)($t194) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:219:13+58
    call $t195 := $CastU128($t194);
    if ($abort_flag) {
        assume {:print "$at(13,7183,7241)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t196 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:219:75+4
    $t196 := 64;
    assume $IsValid'u8'($t196);

    // $t197 := >>($t195, $t196) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:219:13+66
    call $t197 := $ShrU128($t195, $t196);
    if ($abort_flag) {
        assume {:print "$at(13,7183,7249)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,2):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t19 := $t197 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:219:13+66
    $t19 := $t197;

    // trace_local[$t192]($t197) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:219:13+66
    assume {:print "$track_local(101,2,19):", $t197} $t197 == $t197;

    // label L36 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:224:9+5
    assume {:print "$at(13,7305,7310)"} true;
L36:

    // trace_return[0]($t19) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:224:9+5
    assume {:print "$at(13,7305,7310)"} true;
    assume {:print "$track_return(101,2,0):", $t19} $t19 == $t19;

    // goto L54 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:224:9+5
    goto L54;

    // label L34 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:221:13+5
    assume {:print "$at(13,7279,7284)"} true;
L34:

    // $t19 := $t18 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:221:13+5
    assume {:print "$at(13,7279,7284)"} true;
    $t19 := $t18;

    // trace_local[$t192]($t18) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:221:13+5
    assume {:print "$track_local(101,2,19):", $t18} $t18 == $t18;

    // goto L36 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:221:13+5
    goto L36;

    // label L32 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:216:13+5
    assume {:print "$at(13,7103,7108)"} true;
L32:

    // $t18 := $t17 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:216:13+5
    assume {:print "$at(13,7103,7108)"} true;
    $t18 := $t17;

    // trace_local[$t181]($t17) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:216:13+5
    assume {:print "$track_local(101,2,18):", $t17} $t17 == $t17;

    // goto L37 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:216:13+5
    goto L37;

    // label L30 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:211:13+5
    assume {:print "$at(13,6924,6929)"} true;
L30:

    // $t17 := $t16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:211:13+5
    assume {:print "$at(13,6924,6929)"} true;
    $t17 := $t16;

    // trace_local[$t170]($t16) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:211:13+5
    assume {:print "$track_local(101,2,17):", $t16} $t16 == $t16;

    // goto L38 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:211:13+5
    goto L38;

    // label L28 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:206:13+5
    assume {:print "$at(13,6744,6749)"} true;
L28:

    // $t16 := $t15 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:206:13+5
    assume {:print "$at(13,6744,6749)"} true;
    $t16 := $t15;

    // trace_local[$t159]($t15) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:206:13+5
    assume {:print "$track_local(101,2,16):", $t15} $t15 == $t15;

    // goto L39 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:206:13+5
    goto L39;

    // label L26 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:201:13+5
    assume {:print "$at(13,6564,6569)"} true;
L26:

    // $t15 := $t14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:201:13+5
    assume {:print "$at(13,6564,6569)"} true;
    $t15 := $t14;

    // trace_local[$t148]($t14) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:201:13+5
    assume {:print "$track_local(101,2,15):", $t14} $t14 == $t14;

    // goto L40 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:201:13+5
    goto L40;

    // label L24 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:196:13+5
    assume {:print "$at(13,6384,6389)"} true;
L24:

    // $t14 := $t13 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:196:13+5
    assume {:print "$at(13,6384,6389)"} true;
    $t14 := $t13;

    // trace_local[$t137]($t13) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:196:13+5
    assume {:print "$track_local(101,2,14):", $t13} $t13 == $t13;

    // goto L41 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:196:13+5
    goto L41;

    // label L22 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:191:13+5
    assume {:print "$at(13,6203,6208)"} true;
L22:

    // $t13 := $t12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:191:13+5
    assume {:print "$at(13,6203,6208)"} true;
    $t13 := $t12;

    // trace_local[$t126]($t12) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:191:13+5
    assume {:print "$track_local(101,2,13):", $t12} $t12 == $t12;

    // goto L42 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:191:13+5
    goto L42;

    // label L20 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:186:13+5
    assume {:print "$at(13,6022,6027)"} true;
L20:

    // $t12 := $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:186:13+5
    assume {:print "$at(13,6022,6027)"} true;
    $t12 := $t11;

    // trace_local[$t115]($t11) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:186:13+5
    assume {:print "$track_local(101,2,12):", $t11} $t11 == $t11;

    // goto L43 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:186:13+5
    goto L43;

    // label L18 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:181:13+5
    assume {:print "$at(13,5842,5847)"} true;
L18:

    // $t11 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:181:13+5
    assume {:print "$at(13,5842,5847)"} true;
    $t11 := $t10;

    // trace_local[$t104]($t10) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:181:13+5
    assume {:print "$track_local(101,2,11):", $t10} $t10 == $t10;

    // goto L44 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:181:13+5
    goto L44;

    // label L16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:176:13+5
    assume {:print "$at(13,5662,5667)"} true;
L16:

    // $t10 := $t9 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:176:13+5
    assume {:print "$at(13,5662,5667)"} true;
    $t10 := $t9;

    // trace_local[$t93]($t9) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:176:13+5
    assume {:print "$track_local(101,2,10):", $t9} $t9 == $t9;

    // goto L45 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:176:13+5
    goto L45;

    // label L14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:171:13+5
    assume {:print "$at(13,5482,5487)"} true;
L14:

    // $t9 := $t8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:171:13+5
    assume {:print "$at(13,5482,5487)"} true;
    $t9 := $t8;

    // trace_local[$t82]($t8) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:171:13+5
    assume {:print "$track_local(101,2,9):", $t8} $t8 == $t8;

    // goto L46 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:171:13+5
    goto L46;

    // label L12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:166:13+5
    assume {:print "$at(13,5302,5307)"} true;
L12:

    // $t8 := $t7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:166:13+5
    assume {:print "$at(13,5302,5307)"} true;
    $t8 := $t7;

    // trace_local[$t71]($t7) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:166:13+5
    assume {:print "$track_local(101,2,8):", $t7} $t7 == $t7;

    // goto L47 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:166:13+5
    goto L47;

    // label L10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:161:13+5
    assume {:print "$at(13,5123,5128)"} true;
L10:

    // $t7 := $t6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:161:13+5
    assume {:print "$at(13,5123,5128)"} true;
    $t7 := $t6;

    // trace_local[$t60]($t6) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:161:13+5
    assume {:print "$track_local(101,2,7):", $t6} $t6 == $t6;

    // goto L48 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:161:13+5
    goto L48;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:156:13+5
    assume {:print "$at(13,4944,4949)"} true;
L8:

    // $t6 := $t5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:156:13+5
    assume {:print "$at(13,4944,4949)"} true;
    $t6 := $t5;

    // trace_local[$t49]($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:156:13+5
    assume {:print "$track_local(101,2,6):", $t5} $t5 == $t5;

    // goto L49 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:156:13+5
    goto L49;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:151:13+5
    assume {:print "$at(13,4764,4769)"} true;
L6:

    // $t5 := $t4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:151:13+5
    assume {:print "$at(13,4764,4769)"} true;
    $t5 := $t4;

    // trace_local[$t38]($t4) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:151:13+5
    assume {:print "$track_local(101,2,5):", $t4} $t4 == $t4;

    // goto L50 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:151:13+5
    goto L50;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:146:13+5
    assume {:print "$at(13,4584,4589)"} true;
L4:

    // $t4 := $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:146:13+5
    assume {:print "$at(13,4584,4589)"} true;
    $t4 := $t3;

    // trace_local[$t27]($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:146:13+5
    assume {:print "$track_local(101,2,4):", $t3} $t3 == $t3;

    // goto L51 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:146:13+5
    goto L51;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:141:13+5
    assume {:print "$at(13,4406,4411)"} true;
L2:

    // $t3 := $t2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:141:13+5
    assume {:print "$at(13,4406,4411)"} true;
    $t3 := $t2;

    // trace_local[$t16]($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:141:13+5
    assume {:print "$track_local(101,2,3):", $t2} $t2 == $t2;

    // goto L52 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:141:13+5
    goto L52;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:136:13+24
    assume {:print "$at(13,4209,4233)"} true;
L0:

    // $t198 := 18446744073709551616 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:136:13+24
    assume {:print "$at(13,4209,4233)"} true;
    $t198 := 18446744073709551616;
    assume $IsValid'u128'($t198);

    // $t2 := $t198 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:136:13+24
    $t2 := $t198;

    // trace_local[ratio]($t198) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:136:13+24
    assume {:print "$track_local(101,2,2):", $t198} $t198 == $t198;

    // goto L53 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:136:13+24
    goto L53;

    // label L54 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:225:5+1
    assume {:print "$at(13,7315,7316)"} true;
L54:

    // return $t19 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:225:5+1
    assume {:print "$at(13,7315,7316)"} true;
    $ret0 := $t19;
    return;

    // label L55 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:225:5+1
L55:

    // abort($t21) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:225:5+1
    assume {:print "$at(13,7315,7316)"} true;
    $abort_code := $t21;
    $abort_flag := true;
    return;

}

// fun tick_math::get_sqrt_price_at_positive_tick [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:227:5+3631
procedure {:inline 1} $aa_tick_math_get_sqrt_price_at_positive_tick(_$t0: $aa_i32_I32) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: $aa_i32_I32;
    var $t21: int;
    var $t22: bv32;
    var $t23: int;
    var $t24: bv32;
    var $t25: bv32;
    var $t26: bool;
    var $t27: int;
    var $t28: int;
    var $t29: bv32;
    var $t30: bv32;
    var $t31: bool;
    var $t32: int;
    var $t33: int;
    var $t34: int;
    var $t35: int;
    var $t36: int;
    var $t37: int;
    var $t38: int;
    var $t39: bv32;
    var $t40: bv32;
    var $t41: bool;
    var $t42: int;
    var $t43: int;
    var $t44: int;
    var $t45: int;
    var $t46: int;
    var $t47: int;
    var $t48: int;
    var $t49: bv32;
    var $t50: bv32;
    var $t51: bool;
    var $t52: int;
    var $t53: int;
    var $t54: int;
    var $t55: int;
    var $t56: int;
    var $t57: int;
    var $t58: int;
    var $t59: bv32;
    var $t60: bv32;
    var $t61: bool;
    var $t62: int;
    var $t63: int;
    var $t64: int;
    var $t65: int;
    var $t66: int;
    var $t67: int;
    var $t68: int;
    var $t69: bv32;
    var $t70: bv32;
    var $t71: bool;
    var $t72: int;
    var $t73: int;
    var $t74: int;
    var $t75: int;
    var $t76: int;
    var $t77: int;
    var $t78: int;
    var $t79: bv32;
    var $t80: bv32;
    var $t81: bool;
    var $t82: int;
    var $t83: int;
    var $t84: int;
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
    var $t96: int;
    var $t97: int;
    var $t98: int;
    var $t99: bv32;
    var $t100: bv32;
    var $t101: bool;
    var $t102: int;
    var $t103: int;
    var $t104: int;
    var $t105: int;
    var $t106: int;
    var $t107: int;
    var $t108: int;
    var $t109: bv32;
    var $t110: bv32;
    var $t111: bool;
    var $t112: int;
    var $t113: int;
    var $t114: int;
    var $t115: int;
    var $t116: int;
    var $t117: int;
    var $t118: int;
    var $t119: bv32;
    var $t120: bv32;
    var $t121: bool;
    var $t122: int;
    var $t123: int;
    var $t124: int;
    var $t125: int;
    var $t126: int;
    var $t127: int;
    var $t128: int;
    var $t129: bv32;
    var $t130: bv32;
    var $t131: bool;
    var $t132: int;
    var $t133: int;
    var $t134: int;
    var $t135: int;
    var $t136: int;
    var $t137: int;
    var $t138: int;
    var $t139: bv32;
    var $t140: bv32;
    var $t141: bool;
    var $t142: int;
    var $t143: int;
    var $t144: int;
    var $t145: int;
    var $t146: int;
    var $t147: int;
    var $t148: int;
    var $t149: bv32;
    var $t150: bv32;
    var $t151: bool;
    var $t152: int;
    var $t153: int;
    var $t154: int;
    var $t155: int;
    var $t156: int;
    var $t157: int;
    var $t158: int;
    var $t159: bv32;
    var $t160: bv32;
    var $t161: bool;
    var $t162: int;
    var $t163: int;
    var $t164: int;
    var $t165: int;
    var $t166: int;
    var $t167: int;
    var $t168: int;
    var $t169: bv32;
    var $t170: bv32;
    var $t171: bool;
    var $t172: int;
    var $t173: int;
    var $t174: int;
    var $t175: int;
    var $t176: int;
    var $t177: int;
    var $t178: int;
    var $t179: bv32;
    var $t180: bv32;
    var $t181: bool;
    var $t182: int;
    var $t183: int;
    var $t184: int;
    var $t185: int;
    var $t186: int;
    var $t187: int;
    var $t188: int;
    var $t189: bv32;
    var $t190: bv32;
    var $t191: bool;
    var $t192: int;
    var $t193: int;
    var $t194: int;
    var $t195: int;
    var $t196: int;
    var $t197: int;
    var $t198: int;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'u128': int;
    var $temp_0'bv32': bv32;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[tick]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:227:5+1
    assume {:print "$at(13,7322,7323)"} true;
    assume {:print "$track_local(101,3,0):", $t0} $t0 == $t0;

    // $t20 := i32::abs($t0) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:228:36+14
    assume {:print "$at(13,7417,7431)"} true;
    call $t20 := $aa_i32_abs($t0);
    if ($abort_flag) {
        assume {:print "$at(13,7417,7431)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t22 := i32::as_u32($t20) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:228:24+27
    call $t22 := $aa_i32_as_u32($t20);
    if ($abort_flag) {
        assume {:print "$at(13,7405,7432)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // trace_local[abs_tick]($t22) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:228:24+27
    assume {:print "$track_local(101,3,1):", $t22} $t22 == $t22;

    // $t23 := 1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:230:36+3
    assume {:print "$at(13,7532,7535)"} true;
    $t23 := 1;
    assume $IsValid'u32'($t23);

    // $t24 := &($t22, $t23) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:230:25+14
    call $t24 := $AndBv32($t22, $int2bv.32($t23));

    // $t25 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:230:43+1
    $t25 := 0bv32;
    assume $IsValid'bv32'($t25);

    // $t26 := !=($t24, $t25) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:230:25+19
    $t26 := !$IsEqual'bv32'($t24, $t25);

    // if ($t26) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:230:21+127
    if ($t26) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:231:13+24
    assume {:print "$at(13,7556,7580)"} true;
L1:

    // $t27 := 18445821805675392311 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:231:13+24
    assume {:print "$at(13,7556,7580)"} true;
    $t27 := 18445821805675392311;
    assume $IsValid'u128'($t27);

    // $t2 := $t27 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:231:13+24
    $t2 := $t27;

    // trace_local[ratio]($t27) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:231:13+24
    assume {:print "$track_local(101,3,2):", $t27} $t27 == $t27;

    // label L53 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:237:25+8
    assume {:print "$at(13,7755,7763)"} true;
L53:

    // $t28 := 4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:237:36+3
    assume {:print "$at(13,7766,7769)"} true;
    $t28 := 4;
    assume $IsValid'u32'($t28);

    // $t29 := &($t22, $t28) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:237:25+14
    call $t29 := $AndBv32($t22, $int2bv.32($t28));

    // $t30 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:237:43+1
    $t30 := 0bv32;
    assume $IsValid'bv32'($t30);

    // $t31 := !=($t29, $t30) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:237:25+19
    $t31 := !$IsEqual'bv32'($t29, $t30);

    // if ($t31) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:237:21+156
    if ($t31) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:238:15+15
    assume {:print "$at(13,7792,7807)"} true;
L3:

    // $t32 := (u256)($t2) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:238:15+15
    assume {:print "$at(13,7792,7807)"} true;
    call $t32 := $CastU256($t2);
    if ($abort_flag) {
        assume {:print "$at(13,7792,7807)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t33 := 18443055278223354162 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:238:33+34
    $t33 := 18443055278223354162;
    assume $IsValid'u256'($t33);

    // $t34 := *($t32, $t33) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:238:14+54
    call $t34 := $MulU256($t32, $t33);
    if ($abort_flag) {
        assume {:print "$at(13,7791,7845)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t35 := (u128)($t34) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:238:13+64
    call $t35 := $CastU128($t34);
    if ($abort_flag) {
        assume {:print "$at(13,7790,7854)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t36 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:238:81+4
    $t36 := 64;
    assume $IsValid'u8'($t36);

    // $t37 := >>($t35, $t36) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:238:13+72
    call $t37 := $ShrU128($t35, $t36);
    if ($abort_flag) {
        assume {:print "$at(13,7790,7862)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t3 := $t37 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:238:13+72
    $t3 := $t37;

    // trace_local[$t16]($t37) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:238:13+72
    assume {:print "$track_local(101,3,3):", $t37} $t37 == $t37;

    // label L52 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:243:25+8
    assume {:print "$at(13,7942,7950)"} true;
L52:

    // $t38 := 8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:243:36+3
    assume {:print "$at(13,7953,7956)"} true;
    $t38 := 8;
    assume $IsValid'u32'($t38);

    // $t39 := &($t22, $t38) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:243:25+14
    call $t39 := $AndBv32($t22, $int2bv.32($t38));

    // $t40 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:243:43+1
    $t40 := 0bv32;
    assume $IsValid'bv32'($t40);

    // $t41 := !=($t39, $t40) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:243:25+19
    $t41 := !$IsEqual'bv32'($t39, $t40);

    // if ($t41) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:243:21+156
    if ($t41) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:244:15+15
    assume {:print "$at(13,7979,7994)"} true;
L5:

    // $t42 := (u256)($t3) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:244:15+15
    assume {:print "$at(13,7979,7994)"} true;
    call $t42 := $CastU256($t3);
    if ($abort_flag) {
        assume {:print "$at(13,7979,7994)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t43 := 18439367220385604838 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:244:33+34
    $t43 := 18439367220385604838;
    assume $IsValid'u256'($t43);

    // $t44 := *($t42, $t43) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:244:14+54
    call $t44 := $MulU256($t42, $t43);
    if ($abort_flag) {
        assume {:print "$at(13,7978,8032)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t45 := (u128)($t44) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:244:13+64
    call $t45 := $CastU128($t44);
    if ($abort_flag) {
        assume {:print "$at(13,7977,8041)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t46 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:244:81+4
    $t46 := 64;
    assume $IsValid'u8'($t46);

    // $t47 := >>($t45, $t46) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:244:13+72
    call $t47 := $ShrU128($t45, $t46);
    if ($abort_flag) {
        assume {:print "$at(13,7977,8049)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t4 := $t47 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:244:13+72
    $t4 := $t47;

    // trace_local[$t27]($t47) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:244:13+72
    assume {:print "$track_local(101,3,4):", $t47} $t47 == $t47;

    // label L51 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:249:25+8
    assume {:print "$at(13,8129,8137)"} true;
L51:

    // $t48 := 16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:249:36+4
    assume {:print "$at(13,8140,8144)"} true;
    $t48 := 16;
    assume $IsValid'u32'($t48);

    // $t49 := &($t22, $t48) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:249:25+15
    call $t49 := $AndBv32($t22, $int2bv.32($t48));

    // $t50 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:249:44+1
    $t50 := 0bv32;
    assume $IsValid'bv32'($t50);

    // $t51 := !=($t49, $t50) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:249:25+20
    $t51 := !$IsEqual'bv32'($t49, $t50);

    // if ($t51) goto L7 else goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:249:21+157
    if ($t51) { goto L7; } else { goto L6; }

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:250:15+15
    assume {:print "$at(13,8167,8182)"} true;
L7:

    // $t52 := (u256)($t4) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:250:15+15
    assume {:print "$at(13,8167,8182)"} true;
    call $t52 := $CastU256($t4);
    if ($abort_flag) {
        assume {:print "$at(13,8167,8182)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t53 := 18431993317065449817 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:250:33+34
    $t53 := 18431993317065449817;
    assume $IsValid'u256'($t53);

    // $t54 := *($t52, $t53) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:250:14+54
    call $t54 := $MulU256($t52, $t53);
    if ($abort_flag) {
        assume {:print "$at(13,8166,8220)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t55 := (u128)($t54) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:250:13+64
    call $t55 := $CastU128($t54);
    if ($abort_flag) {
        assume {:print "$at(13,8165,8229)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t56 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:250:81+4
    $t56 := 64;
    assume $IsValid'u8'($t56);

    // $t57 := >>($t55, $t56) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:250:13+72
    call $t57 := $ShrU128($t55, $t56);
    if ($abort_flag) {
        assume {:print "$at(13,8165,8237)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t5 := $t57 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:250:13+72
    $t5 := $t57;

    // trace_local[$t38]($t57) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:250:13+72
    assume {:print "$track_local(101,3,5):", $t57} $t57 == $t57;

    // label L50 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:255:25+8
    assume {:print "$at(13,8317,8325)"} true;
L50:

    // $t58 := 32 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:255:36+4
    assume {:print "$at(13,8328,8332)"} true;
    $t58 := 32;
    assume $IsValid'u32'($t58);

    // $t59 := &($t22, $t58) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:255:25+15
    call $t59 := $AndBv32($t22, $int2bv.32($t58));

    // $t60 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:255:44+1
    $t60 := 0bv32;
    assume $IsValid'bv32'($t60);

    // $t61 := !=($t59, $t60) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:255:25+20
    $t61 := !$IsEqual'bv32'($t59, $t60);

    // if ($t61) goto L9 else goto L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:255:21+157
    if ($t61) { goto L9; } else { goto L8; }

    // label L9 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:256:15+15
    assume {:print "$at(13,8355,8370)"} true;
L9:

    // $t62 := (u256)($t5) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:256:15+15
    assume {:print "$at(13,8355,8370)"} true;
    call $t62 := $CastU256($t5);
    if ($abort_flag) {
        assume {:print "$at(13,8355,8370)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t63 := 18417254355718160513 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:256:33+34
    $t63 := 18417254355718160513;
    assume $IsValid'u256'($t63);

    // $t64 := *($t62, $t63) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:256:14+54
    call $t64 := $MulU256($t62, $t63);
    if ($abort_flag) {
        assume {:print "$at(13,8354,8408)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t65 := (u128)($t64) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:256:13+64
    call $t65 := $CastU128($t64);
    if ($abort_flag) {
        assume {:print "$at(13,8353,8417)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t66 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:256:81+4
    $t66 := 64;
    assume $IsValid'u8'($t66);

    // $t67 := >>($t65, $t66) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:256:13+72
    call $t67 := $ShrU128($t65, $t66);
    if ($abort_flag) {
        assume {:print "$at(13,8353,8425)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t6 := $t67 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:256:13+72
    $t6 := $t67;

    // trace_local[$t49]($t67) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:256:13+72
    assume {:print "$track_local(101,3,6):", $t67} $t67 == $t67;

    // label L49 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:261:25+8
    assume {:print "$at(13,8505,8513)"} true;
L49:

    // $t68 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:261:36+4
    assume {:print "$at(13,8516,8520)"} true;
    $t68 := 64;
    assume $IsValid'u32'($t68);

    // $t69 := &($t22, $t68) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:261:25+15
    call $t69 := $AndBv32($t22, $int2bv.32($t68));

    // $t70 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:261:44+1
    $t70 := 0bv32;
    assume $IsValid'bv32'($t70);

    // $t71 := !=($t69, $t70) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:261:25+20
    $t71 := !$IsEqual'bv32'($t69, $t70);

    // if ($t71) goto L11 else goto L10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:261:21+157
    if ($t71) { goto L11; } else { goto L10; }

    // label L11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:262:15+15
    assume {:print "$at(13,8543,8558)"} true;
L11:

    // $t72 := (u256)($t6) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:262:15+15
    assume {:print "$at(13,8543,8558)"} true;
    call $t72 := $CastU256($t6);
    if ($abort_flag) {
        assume {:print "$at(13,8543,8558)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t73 := 18387811781193591352 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:262:33+34
    $t73 := 18387811781193591352;
    assume $IsValid'u256'($t73);

    // $t74 := *($t72, $t73) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:262:14+54
    call $t74 := $MulU256($t72, $t73);
    if ($abort_flag) {
        assume {:print "$at(13,8542,8596)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t75 := (u128)($t74) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:262:13+64
    call $t75 := $CastU128($t74);
    if ($abort_flag) {
        assume {:print "$at(13,8541,8605)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t76 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:262:81+4
    $t76 := 64;
    assume $IsValid'u8'($t76);

    // $t77 := >>($t75, $t76) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:262:13+72
    call $t77 := $ShrU128($t75, $t76);
    if ($abort_flag) {
        assume {:print "$at(13,8541,8613)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t7 := $t77 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:262:13+72
    $t7 := $t77;

    // trace_local[$t60]($t77) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:262:13+72
    assume {:print "$track_local(101,3,7):", $t77} $t77 == $t77;

    // label L48 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:267:25+8
    assume {:print "$at(13,8693,8701)"} true;
L48:

    // $t78 := 128 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:267:36+4
    assume {:print "$at(13,8704,8708)"} true;
    $t78 := 128;
    assume $IsValid'u32'($t78);

    // $t79 := &($t22, $t78) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:267:25+15
    call $t79 := $AndBv32($t22, $int2bv.32($t78));

    // $t80 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:267:44+1
    $t80 := 0bv32;
    assume $IsValid'bv32'($t80);

    // $t81 := !=($t79, $t80) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:267:25+20
    $t81 := !$IsEqual'bv32'($t79, $t80);

    // if ($t81) goto L13 else goto L12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:267:21+157
    if ($t81) { goto L13; } else { goto L12; }

    // label L13 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:268:15+15
    assume {:print "$at(13,8731,8746)"} true;
L13:

    // $t82 := (u256)($t7) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:268:15+15
    assume {:print "$at(13,8731,8746)"} true;
    call $t82 := $CastU256($t7);
    if ($abort_flag) {
        assume {:print "$at(13,8731,8746)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t83 := 18329067761203520168 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:268:33+34
    $t83 := 18329067761203520168;
    assume $IsValid'u256'($t83);

    // $t84 := *($t82, $t83) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:268:14+54
    call $t84 := $MulU256($t82, $t83);
    if ($abort_flag) {
        assume {:print "$at(13,8730,8784)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t85 := (u128)($t84) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:268:13+64
    call $t85 := $CastU128($t84);
    if ($abort_flag) {
        assume {:print "$at(13,8729,8793)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t86 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:268:81+4
    $t86 := 64;
    assume $IsValid'u8'($t86);

    // $t87 := >>($t85, $t86) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:268:13+72
    call $t87 := $ShrU128($t85, $t86);
    if ($abort_flag) {
        assume {:print "$at(13,8729,8801)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t8 := $t87 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:268:13+72
    $t8 := $t87;

    // trace_local[$t71]($t87) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:268:13+72
    assume {:print "$track_local(101,3,8):", $t87} $t87 == $t87;

    // label L47 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:273:25+8
    assume {:print "$at(13,8881,8889)"} true;
L47:

    // $t88 := 256 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:273:36+5
    assume {:print "$at(13,8892,8897)"} true;
    $t88 := 256;
    assume $IsValid'u32'($t88);

    // $t89 := &($t22, $t88) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:273:25+16
    call $t89 := $AndBv32($t22, $int2bv.32($t88));

    // $t90 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:273:45+1
    $t90 := 0bv32;
    assume $IsValid'bv32'($t90);

    // $t91 := !=($t89, $t90) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:273:25+21
    $t91 := !$IsEqual'bv32'($t89, $t90);

    // if ($t91) goto L15 else goto L14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:273:21+158
    if ($t91) { goto L15; } else { goto L14; }

    // label L15 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:274:15+15
    assume {:print "$at(13,8920,8935)"} true;
L15:

    // $t92 := (u256)($t8) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:274:15+15
    assume {:print "$at(13,8920,8935)"} true;
    call $t92 := $CastU256($t8);
    if ($abort_flag) {
        assume {:print "$at(13,8920,8935)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t93 := 18212142134806087854 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:274:33+34
    $t93 := 18212142134806087854;
    assume $IsValid'u256'($t93);

    // $t94 := *($t92, $t93) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:274:14+54
    call $t94 := $MulU256($t92, $t93);
    if ($abort_flag) {
        assume {:print "$at(13,8919,8973)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t95 := (u128)($t94) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:274:13+64
    call $t95 := $CastU128($t94);
    if ($abort_flag) {
        assume {:print "$at(13,8918,8982)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t96 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:274:81+4
    $t96 := 64;
    assume $IsValid'u8'($t96);

    // $t97 := >>($t95, $t96) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:274:13+72
    call $t97 := $ShrU128($t95, $t96);
    if ($abort_flag) {
        assume {:print "$at(13,8918,8990)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t9 := $t97 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:274:13+72
    $t9 := $t97;

    // trace_local[$t82]($t97) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:274:13+72
    assume {:print "$track_local(101,3,9):", $t97} $t97 == $t97;

    // label L46 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:279:25+8
    assume {:print "$at(13,9070,9078)"} true;
L46:

    // $t98 := 512 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:279:36+5
    assume {:print "$at(13,9081,9086)"} true;
    $t98 := 512;
    assume $IsValid'u32'($t98);

    // $t99 := &($t22, $t98) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:279:25+16
    call $t99 := $AndBv32($t22, $int2bv.32($t98));

    // $t100 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:279:45+1
    $t100 := 0bv32;
    assume $IsValid'bv32'($t100);

    // $t101 := !=($t99, $t100) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:279:25+21
    $t101 := !$IsEqual'bv32'($t99, $t100);

    // if ($t101) goto L17 else goto L16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:279:21+158
    if ($t101) { goto L17; } else { goto L16; }

    // label L17 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:280:15+15
    assume {:print "$at(13,9109,9124)"} true;
L17:

    // $t102 := (u256)($t9) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:280:15+15
    assume {:print "$at(13,9109,9124)"} true;
    call $t102 := $CastU256($t9);
    if ($abort_flag) {
        assume {:print "$at(13,9109,9124)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t103 := 17980523815641551639 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:280:33+34
    $t103 := 17980523815641551639;
    assume $IsValid'u256'($t103);

    // $t104 := *($t102, $t103) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:280:14+54
    call $t104 := $MulU256($t102, $t103);
    if ($abort_flag) {
        assume {:print "$at(13,9108,9162)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t105 := (u128)($t104) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:280:13+64
    call $t105 := $CastU128($t104);
    if ($abort_flag) {
        assume {:print "$at(13,9107,9171)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t106 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:280:81+4
    $t106 := 64;
    assume $IsValid'u8'($t106);

    // $t107 := >>($t105, $t106) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:280:13+72
    call $t107 := $ShrU128($t105, $t106);
    if ($abort_flag) {
        assume {:print "$at(13,9107,9179)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t10 := $t107 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:280:13+72
    $t10 := $t107;

    // trace_local[$t93]($t107) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:280:13+72
    assume {:print "$track_local(101,3,10):", $t107} $t107 == $t107;

    // label L45 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:285:25+8
    assume {:print "$at(13,9259,9267)"} true;
L45:

    // $t108 := 1024 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:285:36+5
    assume {:print "$at(13,9270,9275)"} true;
    $t108 := 1024;
    assume $IsValid'u32'($t108);

    // $t109 := &($t22, $t108) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:285:25+16
    call $t109 := $AndBv32($t22, $int2bv.32($t108));

    // $t110 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:285:45+1
    $t110 := 0bv32;
    assume $IsValid'bv32'($t110);

    // $t111 := !=($t109, $t110) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:285:25+21
    $t111 := !$IsEqual'bv32'($t109, $t110);

    // if ($t111) goto L19 else goto L18 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:285:21+158
    if ($t111) { goto L19; } else { goto L18; }

    // label L19 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:286:15+15
    assume {:print "$at(13,9298,9313)"} true;
L19:

    // $t112 := (u256)($t10) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:286:15+15
    assume {:print "$at(13,9298,9313)"} true;
    call $t112 := $CastU256($t10);
    if ($abort_flag) {
        assume {:print "$at(13,9298,9313)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t113 := 17526086738831147013 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:286:33+34
    $t113 := 17526086738831147013;
    assume $IsValid'u256'($t113);

    // $t114 := *($t112, $t113) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:286:14+54
    call $t114 := $MulU256($t112, $t113);
    if ($abort_flag) {
        assume {:print "$at(13,9297,9351)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t115 := (u128)($t114) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:286:13+64
    call $t115 := $CastU128($t114);
    if ($abort_flag) {
        assume {:print "$at(13,9296,9360)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t116 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:286:81+4
    $t116 := 64;
    assume $IsValid'u8'($t116);

    // $t117 := >>($t115, $t116) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:286:13+72
    call $t117 := $ShrU128($t115, $t116);
    if ($abort_flag) {
        assume {:print "$at(13,9296,9368)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t11 := $t117 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:286:13+72
    $t11 := $t117;

    // trace_local[$t104]($t117) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:286:13+72
    assume {:print "$track_local(101,3,11):", $t117} $t117 == $t117;

    // label L44 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:291:25+8
    assume {:print "$at(13,9448,9456)"} true;
L44:

    // $t118 := 2048 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:291:36+5
    assume {:print "$at(13,9459,9464)"} true;
    $t118 := 2048;
    assume $IsValid'u32'($t118);

    // $t119 := &($t22, $t118) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:291:25+16
    call $t119 := $AndBv32($t22, $int2bv.32($t118));

    // $t120 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:291:45+1
    $t120 := 0bv32;
    assume $IsValid'bv32'($t120);

    // $t121 := !=($t119, $t120) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:291:25+21
    $t121 := !$IsEqual'bv32'($t119, $t120);

    // if ($t121) goto L21 else goto L20 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:291:21+158
    if ($t121) { goto L21; } else { goto L20; }

    // label L21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:292:15+15
    assume {:print "$at(13,9487,9502)"} true;
L21:

    // $t122 := (u256)($t11) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:292:15+15
    assume {:print "$at(13,9487,9502)"} true;
    call $t122 := $CastU256($t11);
    if ($abort_flag) {
        assume {:print "$at(13,9487,9502)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t123 := 16651378430235024244 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:292:33+34
    $t123 := 16651378430235024244;
    assume $IsValid'u256'($t123);

    // $t124 := *($t122, $t123) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:292:14+54
    call $t124 := $MulU256($t122, $t123);
    if ($abort_flag) {
        assume {:print "$at(13,9486,9540)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t125 := (u128)($t124) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:292:13+64
    call $t125 := $CastU128($t124);
    if ($abort_flag) {
        assume {:print "$at(13,9485,9549)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t126 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:292:81+4
    $t126 := 64;
    assume $IsValid'u8'($t126);

    // $t127 := >>($t125, $t126) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:292:13+72
    call $t127 := $ShrU128($t125, $t126);
    if ($abort_flag) {
        assume {:print "$at(13,9485,9557)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t12 := $t127 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:292:13+72
    $t12 := $t127;

    // trace_local[$t115]($t127) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:292:13+72
    assume {:print "$track_local(101,3,12):", $t127} $t127 == $t127;

    // label L43 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:297:25+8
    assume {:print "$at(13,9637,9645)"} true;
L43:

    // $t128 := 4096 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:297:36+6
    assume {:print "$at(13,9648,9654)"} true;
    $t128 := 4096;
    assume $IsValid'u32'($t128);

    // $t129 := &($t22, $t128) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:297:25+17
    call $t129 := $AndBv32($t22, $int2bv.32($t128));

    // $t130 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:297:46+1
    $t130 := 0bv32;
    assume $IsValid'bv32'($t130);

    // $t131 := !=($t129, $t130) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:297:25+22
    $t131 := !$IsEqual'bv32'($t129, $t130);

    // if ($t131) goto L23 else goto L22 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:297:21+159
    if ($t131) { goto L23; } else { goto L22; }

    // label L23 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:298:15+15
    assume {:print "$at(13,9677,9692)"} true;
L23:

    // $t132 := (u256)($t12) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:298:15+15
    assume {:print "$at(13,9677,9692)"} true;
    call $t132 := $CastU256($t12);
    if ($abort_flag) {
        assume {:print "$at(13,9677,9692)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t133 := 15030750278693429944 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:298:33+34
    $t133 := 15030750278693429944;
    assume $IsValid'u256'($t133);

    // $t134 := *($t132, $t133) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:298:14+54
    call $t134 := $MulU256($t132, $t133);
    if ($abort_flag) {
        assume {:print "$at(13,9676,9730)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t135 := (u128)($t134) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:298:13+64
    call $t135 := $CastU128($t134);
    if ($abort_flag) {
        assume {:print "$at(13,9675,9739)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t136 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:298:81+4
    $t136 := 64;
    assume $IsValid'u8'($t136);

    // $t137 := >>($t135, $t136) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:298:13+72
    call $t137 := $ShrU128($t135, $t136);
    if ($abort_flag) {
        assume {:print "$at(13,9675,9747)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t13 := $t137 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:298:13+72
    $t13 := $t137;

    // trace_local[$t126]($t137) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:298:13+72
    assume {:print "$track_local(101,3,13):", $t137} $t137 == $t137;

    // label L42 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:303:25+8
    assume {:print "$at(13,9827,9835)"} true;
L42:

    // $t138 := 8192 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:303:36+6
    assume {:print "$at(13,9838,9844)"} true;
    $t138 := 8192;
    assume $IsValid'u32'($t138);

    // $t139 := &($t22, $t138) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:303:25+17
    call $t139 := $AndBv32($t22, $int2bv.32($t138));

    // $t140 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:303:46+1
    $t140 := 0bv32;
    assume $IsValid'bv32'($t140);

    // $t141 := !=($t139, $t140) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:303:25+22
    $t141 := !$IsEqual'bv32'($t139, $t140);

    // if ($t141) goto L25 else goto L24 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:303:21+159
    if ($t141) { goto L25; } else { goto L24; }

    // label L25 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:304:15+15
    assume {:print "$at(13,9867,9882)"} true;
L25:

    // $t142 := (u256)($t13) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:304:15+15
    assume {:print "$at(13,9867,9882)"} true;
    call $t142 := $CastU256($t13);
    if ($abort_flag) {
        assume {:print "$at(13,9867,9882)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t143 := 12247334978882834399 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:304:33+34
    $t143 := 12247334978882834399;
    assume $IsValid'u256'($t143);

    // $t144 := *($t142, $t143) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:304:14+54
    call $t144 := $MulU256($t142, $t143);
    if ($abort_flag) {
        assume {:print "$at(13,9866,9920)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t145 := (u128)($t144) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:304:13+64
    call $t145 := $CastU128($t144);
    if ($abort_flag) {
        assume {:print "$at(13,9865,9929)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t146 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:304:81+4
    $t146 := 64;
    assume $IsValid'u8'($t146);

    // $t147 := >>($t145, $t146) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:304:13+72
    call $t147 := $ShrU128($t145, $t146);
    if ($abort_flag) {
        assume {:print "$at(13,9865,9937)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t14 := $t147 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:304:13+72
    $t14 := $t147;

    // trace_local[$t137]($t147) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:304:13+72
    assume {:print "$track_local(101,3,14):", $t147} $t147 == $t147;

    // label L41 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:309:25+8
    assume {:print "$at(13,10017,10025)"} true;
L41:

    // $t148 := 16384 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:309:36+6
    assume {:print "$at(13,10028,10034)"} true;
    $t148 := 16384;
    assume $IsValid'u32'($t148);

    // $t149 := &($t22, $t148) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:309:25+17
    call $t149 := $AndBv32($t22, $int2bv.32($t148));

    // $t150 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:309:46+1
    $t150 := 0bv32;
    assume $IsValid'bv32'($t150);

    // $t151 := !=($t149, $t150) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:309:25+22
    $t151 := !$IsEqual'bv32'($t149, $t150);

    // if ($t151) goto L27 else goto L26 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:309:21+158
    if ($t151) { goto L27; } else { goto L26; }

    // label L27 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:310:15+15
    assume {:print "$at(13,10057,10072)"} true;
L27:

    // $t152 := (u256)($t14) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:310:15+15
    assume {:print "$at(13,10057,10072)"} true;
    call $t152 := $CastU256($t14);
    if ($abort_flag) {
        assume {:print "$at(13,10057,10072)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t153 := 8131365268884726200 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:310:33+33
    $t153 := 8131365268884726200;
    assume $IsValid'u256'($t153);

    // $t154 := *($t152, $t153) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:310:14+53
    call $t154 := $MulU256($t152, $t153);
    if ($abort_flag) {
        assume {:print "$at(13,10056,10109)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t155 := (u128)($t154) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:310:13+63
    call $t155 := $CastU128($t154);
    if ($abort_flag) {
        assume {:print "$at(13,10055,10118)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t156 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:310:80+4
    $t156 := 64;
    assume $IsValid'u8'($t156);

    // $t157 := >>($t155, $t156) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:310:13+71
    call $t157 := $ShrU128($t155, $t156);
    if ($abort_flag) {
        assume {:print "$at(13,10055,10126)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t15 := $t157 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:310:13+71
    $t15 := $t157;

    // trace_local[$t148]($t157) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:310:13+71
    assume {:print "$track_local(101,3,15):", $t157} $t157 == $t157;

    // label L40 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:315:25+8
    assume {:print "$at(13,10206,10214)"} true;
L40:

    // $t158 := 32768 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:315:36+6
    assume {:print "$at(13,10217,10223)"} true;
    $t158 := 32768;
    assume $IsValid'u32'($t158);

    // $t159 := &($t22, $t158) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:315:25+17
    call $t159 := $AndBv32($t22, $int2bv.32($t158));

    // $t160 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:315:46+1
    $t160 := 0bv32;
    assume $IsValid'bv32'($t160);

    // $t161 := !=($t159, $t160) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:315:25+22
    $t161 := !$IsEqual'bv32'($t159, $t160);

    // if ($t161) goto L29 else goto L28 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:315:21+158
    if ($t161) { goto L29; } else { goto L28; }

    // label L29 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:316:15+15
    assume {:print "$at(13,10246,10261)"} true;
L29:

    // $t162 := (u256)($t15) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:316:15+15
    assume {:print "$at(13,10246,10261)"} true;
    call $t162 := $CastU256($t15);
    if ($abort_flag) {
        assume {:print "$at(13,10246,10261)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t163 := 3584323654723342297 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:316:33+33
    $t163 := 3584323654723342297;
    assume $IsValid'u256'($t163);

    // $t164 := *($t162, $t163) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:316:14+53
    call $t164 := $MulU256($t162, $t163);
    if ($abort_flag) {
        assume {:print "$at(13,10245,10298)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t165 := (u128)($t164) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:316:13+63
    call $t165 := $CastU128($t164);
    if ($abort_flag) {
        assume {:print "$at(13,10244,10307)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t166 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:316:80+4
    $t166 := 64;
    assume $IsValid'u8'($t166);

    // $t167 := >>($t165, $t166) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:316:13+71
    call $t167 := $ShrU128($t165, $t166);
    if ($abort_flag) {
        assume {:print "$at(13,10244,10315)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t16 := $t167 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:316:13+71
    $t16 := $t167;

    // trace_local[$t159]($t167) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:316:13+71
    assume {:print "$track_local(101,3,16):", $t167} $t167 == $t167;

    // label L39 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:321:25+8
    assume {:print "$at(13,10395,10403)"} true;
L39:

    // $t168 := 65536 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:321:36+7
    assume {:print "$at(13,10406,10413)"} true;
    $t168 := 65536;
    assume $IsValid'u32'($t168);

    // $t169 := &($t22, $t168) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:321:25+18
    call $t169 := $AndBv32($t22, $int2bv.32($t168));

    // $t170 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:321:47+1
    $t170 := 0bv32;
    assume $IsValid'bv32'($t170);

    // $t171 := !=($t169, $t170) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:321:25+23
    $t171 := !$IsEqual'bv32'($t169, $t170);

    // if ($t171) goto L31 else goto L30 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:321:21+158
    if ($t171) { goto L31; } else { goto L30; }

    // label L31 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:322:15+15
    assume {:print "$at(13,10436,10451)"} true;
L31:

    // $t172 := (u256)($t16) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:322:15+15
    assume {:print "$at(13,10436,10451)"} true;
    call $t172 := $CastU256($t16);
    if ($abort_flag) {
        assume {:print "$at(13,10436,10451)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t173 := 696457651847595233 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:322:33+32
    $t173 := 696457651847595233;
    assume $IsValid'u256'($t173);

    // $t174 := *($t172, $t173) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:322:14+52
    call $t174 := $MulU256($t172, $t173);
    if ($abort_flag) {
        assume {:print "$at(13,10435,10487)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t175 := (u128)($t174) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:322:13+62
    call $t175 := $CastU128($t174);
    if ($abort_flag) {
        assume {:print "$at(13,10434,10496)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t176 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:322:79+4
    $t176 := 64;
    assume $IsValid'u8'($t176);

    // $t177 := >>($t175, $t176) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:322:13+70
    call $t177 := $ShrU128($t175, $t176);
    if ($abort_flag) {
        assume {:print "$at(13,10434,10504)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t17 := $t177 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:322:13+70
    $t17 := $t177;

    // trace_local[$t170]($t177) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:322:13+70
    assume {:print "$track_local(101,3,17):", $t177} $t177 == $t177;

    // label L38 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:327:25+8
    assume {:print "$at(13,10584,10592)"} true;
L38:

    // $t178 := 131072 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:327:36+7
    assume {:print "$at(13,10595,10602)"} true;
    $t178 := 131072;
    assume $IsValid'u32'($t178);

    // $t179 := &($t22, $t178) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:327:25+18
    call $t179 := $AndBv32($t22, $int2bv.32($t178));

    // $t180 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:327:47+1
    $t180 := 0bv32;
    assume $IsValid'bv32'($t180);

    // $t181 := !=($t179, $t180) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:327:25+23
    $t181 := !$IsEqual'bv32'($t179, $t180);

    // if ($t181) goto L33 else goto L32 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:327:21+157
    if ($t181) { goto L33; } else { goto L32; }

    // label L33 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:328:15+15
    assume {:print "$at(13,10625,10640)"} true;
L33:

    // $t182 := (u256)($t17) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:328:15+15
    assume {:print "$at(13,10625,10640)"} true;
    call $t182 := $CastU256($t17);
    if ($abort_flag) {
        assume {:print "$at(13,10625,10640)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t183 := 26294789957452057 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:328:33+31
    $t183 := 26294789957452057;
    assume $IsValid'u256'($t183);

    // $t184 := *($t182, $t183) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:328:14+51
    call $t184 := $MulU256($t182, $t183);
    if ($abort_flag) {
        assume {:print "$at(13,10624,10675)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t185 := (u128)($t184) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:328:13+61
    call $t185 := $CastU128($t184);
    if ($abort_flag) {
        assume {:print "$at(13,10623,10684)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t186 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:328:78+4
    $t186 := 64;
    assume $IsValid'u8'($t186);

    // $t187 := >>($t185, $t186) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:328:13+69
    call $t187 := $ShrU128($t185, $t186);
    if ($abort_flag) {
        assume {:print "$at(13,10623,10692)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t18 := $t187 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:328:13+69
    $t18 := $t187;

    // trace_local[$t181]($t187) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:328:13+69
    assume {:print "$track_local(101,3,18):", $t187} $t187 == $t187;

    // label L37 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:333:25+8
    assume {:print "$at(13,10772,10780)"} true;
L37:

    // $t188 := 262144 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:333:36+7
    assume {:print "$at(13,10783,10790)"} true;
    $t188 := 262144;
    assume $IsValid'u32'($t188);

    // $t189 := &($t22, $t188) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:333:25+18
    call $t189 := $AndBv32($t22, $int2bv.32($t188));

    // $t190 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:333:47+1
    $t190 := 0bv32;
    assume $IsValid'bv32'($t190);

    // $t191 := !=($t189, $t190) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:333:25+23
    $t191 := !$IsEqual'bv32'($t189, $t190);

    // if ($t191) goto L35 else goto L34 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:333:21+154
    if ($t191) { goto L35; } else { goto L34; }

    // label L35 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:334:15+15
    assume {:print "$at(13,10813,10828)"} true;
L35:

    // $t192 := (u256)($t18) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:334:15+15
    assume {:print "$at(13,10813,10828)"} true;
    call $t192 := $CastU256($t18);
    if ($abort_flag) {
        assume {:print "$at(13,10813,10828)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t193 := 37481735321082 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:334:33+28
    $t193 := 37481735321082;
    assume $IsValid'u256'($t193);

    // $t194 := *($t192, $t193) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:334:14+48
    call $t194 := $MulU256($t192, $t193);
    if ($abort_flag) {
        assume {:print "$at(13,10812,10860)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t195 := (u128)($t194) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:334:13+58
    call $t195 := $CastU128($t194);
    if ($abort_flag) {
        assume {:print "$at(13,10811,10869)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t196 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:334:75+4
    $t196 := 64;
    assume $IsValid'u8'($t196);

    // $t197 := >>($t195, $t196) on_abort goto L55 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:334:13+66
    call $t197 := $ShrU128($t195, $t196);
    if ($abort_flag) {
        assume {:print "$at(13,10811,10877)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(101,3):", $t21} $t21 == $t21;
        goto L55;
    }

    // $t19 := $t197 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:334:13+66
    $t19 := $t197;

    // trace_local[$t192]($t197) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:334:13+66
    assume {:print "$track_local(101,3,19):", $t197} $t197 == $t197;

    // label L36 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:339:9+5
    assume {:print "$at(13,10941,10946)"} true;
L36:

    // trace_return[0]($t19) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:339:9+5
    assume {:print "$at(13,10941,10946)"} true;
    assume {:print "$track_return(101,3,0):", $t19} $t19 == $t19;

    // goto L54 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:339:9+5
    goto L54;

    // label L34 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:336:13+5
    assume {:print "$at(13,10907,10912)"} true;
L34:

    // $t19 := $t18 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:336:13+5
    assume {:print "$at(13,10907,10912)"} true;
    $t19 := $t18;

    // trace_local[$t192]($t18) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:336:13+5
    assume {:print "$track_local(101,3,19):", $t18} $t18 == $t18;

    // goto L36 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:336:13+5
    goto L36;

    // label L32 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:330:13+5
    assume {:print "$at(13,10722,10727)"} true;
L32:

    // $t18 := $t17 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:330:13+5
    assume {:print "$at(13,10722,10727)"} true;
    $t18 := $t17;

    // trace_local[$t181]($t17) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:330:13+5
    assume {:print "$track_local(101,3,18):", $t17} $t17 == $t17;

    // goto L37 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:330:13+5
    goto L37;

    // label L30 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:324:13+5
    assume {:print "$at(13,10534,10539)"} true;
L30:

    // $t17 := $t16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:324:13+5
    assume {:print "$at(13,10534,10539)"} true;
    $t17 := $t16;

    // trace_local[$t170]($t16) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:324:13+5
    assume {:print "$track_local(101,3,17):", $t16} $t16 == $t16;

    // goto L38 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:324:13+5
    goto L38;

    // label L28 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:318:13+5
    assume {:print "$at(13,10345,10350)"} true;
L28:

    // $t16 := $t15 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:318:13+5
    assume {:print "$at(13,10345,10350)"} true;
    $t16 := $t15;

    // trace_local[$t159]($t15) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:318:13+5
    assume {:print "$track_local(101,3,16):", $t15} $t15 == $t15;

    // goto L39 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:318:13+5
    goto L39;

    // label L26 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:312:13+5
    assume {:print "$at(13,10156,10161)"} true;
L26:

    // $t15 := $t14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:312:13+5
    assume {:print "$at(13,10156,10161)"} true;
    $t15 := $t14;

    // trace_local[$t148]($t14) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:312:13+5
    assume {:print "$track_local(101,3,15):", $t14} $t14 == $t14;

    // goto L40 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:312:13+5
    goto L40;

    // label L24 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:306:13+5
    assume {:print "$at(13,9967,9972)"} true;
L24:

    // $t14 := $t13 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:306:13+5
    assume {:print "$at(13,9967,9972)"} true;
    $t14 := $t13;

    // trace_local[$t137]($t13) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:306:13+5
    assume {:print "$track_local(101,3,14):", $t13} $t13 == $t13;

    // goto L41 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:306:13+5
    goto L41;

    // label L22 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:300:13+5
    assume {:print "$at(13,9777,9782)"} true;
L22:

    // $t13 := $t12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:300:13+5
    assume {:print "$at(13,9777,9782)"} true;
    $t13 := $t12;

    // trace_local[$t126]($t12) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:300:13+5
    assume {:print "$track_local(101,3,13):", $t12} $t12 == $t12;

    // goto L42 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:300:13+5
    goto L42;

    // label L20 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:294:13+5
    assume {:print "$at(13,9587,9592)"} true;
L20:

    // $t12 := $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:294:13+5
    assume {:print "$at(13,9587,9592)"} true;
    $t12 := $t11;

    // trace_local[$t115]($t11) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:294:13+5
    assume {:print "$track_local(101,3,12):", $t11} $t11 == $t11;

    // goto L43 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:294:13+5
    goto L43;

    // label L18 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:288:13+5
    assume {:print "$at(13,9398,9403)"} true;
L18:

    // $t11 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:288:13+5
    assume {:print "$at(13,9398,9403)"} true;
    $t11 := $t10;

    // trace_local[$t104]($t10) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:288:13+5
    assume {:print "$track_local(101,3,11):", $t10} $t10 == $t10;

    // goto L44 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:288:13+5
    goto L44;

    // label L16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:282:13+5
    assume {:print "$at(13,9209,9214)"} true;
L16:

    // $t10 := $t9 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:282:13+5
    assume {:print "$at(13,9209,9214)"} true;
    $t10 := $t9;

    // trace_local[$t93]($t9) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:282:13+5
    assume {:print "$track_local(101,3,10):", $t9} $t9 == $t9;

    // goto L45 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:282:13+5
    goto L45;

    // label L14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:276:13+5
    assume {:print "$at(13,9020,9025)"} true;
L14:

    // $t9 := $t8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:276:13+5
    assume {:print "$at(13,9020,9025)"} true;
    $t9 := $t8;

    // trace_local[$t82]($t8) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:276:13+5
    assume {:print "$track_local(101,3,9):", $t8} $t8 == $t8;

    // goto L46 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:276:13+5
    goto L46;

    // label L12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:270:13+5
    assume {:print "$at(13,8831,8836)"} true;
L12:

    // $t8 := $t7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:270:13+5
    assume {:print "$at(13,8831,8836)"} true;
    $t8 := $t7;

    // trace_local[$t71]($t7) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:270:13+5
    assume {:print "$track_local(101,3,8):", $t7} $t7 == $t7;

    // goto L47 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:270:13+5
    goto L47;

    // label L10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:264:13+5
    assume {:print "$at(13,8643,8648)"} true;
L10:

    // $t7 := $t6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:264:13+5
    assume {:print "$at(13,8643,8648)"} true;
    $t7 := $t6;

    // trace_local[$t60]($t6) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:264:13+5
    assume {:print "$track_local(101,3,7):", $t6} $t6 == $t6;

    // goto L48 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:264:13+5
    goto L48;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:258:13+5
    assume {:print "$at(13,8455,8460)"} true;
L8:

    // $t6 := $t5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:258:13+5
    assume {:print "$at(13,8455,8460)"} true;
    $t6 := $t5;

    // trace_local[$t49]($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:258:13+5
    assume {:print "$track_local(101,3,6):", $t5} $t5 == $t5;

    // goto L49 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:258:13+5
    goto L49;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:252:13+5
    assume {:print "$at(13,8267,8272)"} true;
L6:

    // $t5 := $t4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:252:13+5
    assume {:print "$at(13,8267,8272)"} true;
    $t5 := $t4;

    // trace_local[$t38]($t4) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:252:13+5
    assume {:print "$track_local(101,3,5):", $t4} $t4 == $t4;

    // goto L50 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:252:13+5
    goto L50;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:246:13+5
    assume {:print "$at(13,8079,8084)"} true;
L4:

    // $t4 := $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:246:13+5
    assume {:print "$at(13,8079,8084)"} true;
    $t4 := $t3;

    // trace_local[$t27]($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:246:13+5
    assume {:print "$track_local(101,3,4):", $t3} $t3 == $t3;

    // goto L51 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:246:13+5
    goto L51;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:240:13+5
    assume {:print "$at(13,7892,7897)"} true;
L2:

    // $t3 := $t2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:240:13+5
    assume {:print "$at(13,7892,7897)"} true;
    $t3 := $t2;

    // trace_local[$t16]($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:240:13+5
    assume {:print "$track_local(101,3,3):", $t2} $t2 == $t2;

    // goto L52 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:240:13+5
    goto L52;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:233:13+24
    assume {:print "$at(13,7610,7634)"} true;
L0:

    // $t198 := 18446744073709551616 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:233:13+24
    assume {:print "$at(13,7610,7634)"} true;
    $t198 := 18446744073709551616;
    assume $IsValid'u128'($t198);

    // $t2 := $t198 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:233:13+24
    $t2 := $t198;

    // trace_local[ratio]($t198) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:233:13+24
    assume {:print "$track_local(101,3,2):", $t198} $t198 == $t198;

    // goto L53 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:233:13+24
    goto L53;

    // label L54 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:341:5+1
    assume {:print "$at(13,10952,10953)"} true;
L54:

    // return $t19 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:341:5+1
    assume {:print "$at(13,10952,10953)"} true;
    $ret0 := $t19;
    return;

    // label L55 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:341:5+1
L55:

    // abort($t21) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:341:5+1
    assume {:print "$at(13,10952,10953)"} true;
    $abort_code := $t21;
    $abort_flag := true;
    return;

}

// fun tick_math::get_sqrt_price_at_tick [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:51:5+316
procedure {:inline 1} $aa_tick_math_get_sqrt_price_at_tick(_$t0: $aa_i32_I32) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: bool;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: $aa_i32_I32;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'u128': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[tick]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:51:5+1
    assume {:print "$at(13,1382,1383)"} true;
    assume {:print "$track_local(101,4,0):", $t0} $t0 == $t0;

    // $t2 := i32::is_neg($t0) on_abort goto L4 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:53:13+17
    assume {:print "$at(13,1545,1562)"} true;
    call $t2 := $aa_i32_is_neg($t0);
    if ($abort_flag) {
        assume {:print "$at(13,1545,1562)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(101,4):", $t3} $t3 == $t3;
        goto L4;
    }

    // if ($t2) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:53:9+151
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:54:13+37
    assume {:print "$at(13,1578,1615)"} true;
L1:

    // $t4 := tick_math::get_sqrt_price_at_negative_tick($t0) on_abort goto L4 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:54:13+37
    assume {:print "$at(13,1578,1615)"} true;
    call $t4 := $aa_tick_math_get_sqrt_price_at_negative_tick($t0);
    if ($abort_flag) {
        assume {:print "$at(13,1578,1615)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(101,4):", $t3} $t3 == $t3;
        goto L4;
    }

    // $t1 := $t4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:54:13+37
    $t1 := $t4;

    // trace_local[return]($t4) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:54:13+37
    assume {:print "$track_local(101,4,1):", $t4} $t4 == $t4;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:53:9+151
    assume {:print "$at(13,1541,1692)"} true;
L2:

    // trace_return[0]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:53:9+151
    assume {:print "$at(13,1541,1692)"} true;
    assume {:print "$track_return(101,4,0):", $t1} $t1 == $t1;

    // goto L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:53:9+151
    goto L3;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:56:13+37
    assume {:print "$at(13,1645,1682)"} true;
L0:

    // $t5 := tick_math::get_sqrt_price_at_positive_tick($t0) on_abort goto L4 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:56:13+37
    assume {:print "$at(13,1645,1682)"} true;
    call $t5 := $aa_tick_math_get_sqrt_price_at_positive_tick($t0);
    if ($abort_flag) {
        assume {:print "$at(13,1645,1682)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(101,4):", $t3} $t3 == $t3;
        goto L4;
    }

    // $t1 := $t5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:56:13+37
    $t1 := $t5;

    // trace_local[return]($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:56:13+37
    assume {:print "$track_local(101,4,1):", $t5} $t5 == $t5;

    // goto L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:56:13+37
    goto L2;

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:58:5+1
    assume {:print "$at(13,1697,1698)"} true;
L3:

    // return $t1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:58:5+1
    assume {:print "$at(13,1697,1698)"} true;
    $ret0 := $t1;
    return;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:58:5+1
L4:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/tick_math.move:58:5+1
    assume {:print "$at(13,1697,1698)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct tick_bitmap::BitMap at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/tick_bitmap.move:10:5+61
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

// fun liquidity_math::sub_delta [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/liquidity_math.move:9:5+78
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
    // trace_local[net]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/liquidity_math.move:9:5+1
    assume {:print "$at(9,178,179)"} true;
    assume {:print "$track_local(105,1,0):", $t0} $t0 == $t0;

    // trace_local[delta]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/liquidity_math.move:9:5+1
    assume {:print "$track_local(105,1,1):", $t1} $t1 == $t1;

    // $t2 := -($t0, $t1) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/liquidity_math.move:10:9+11
    assume {:print "$at(9,239,250)"} true;
    call $t2 := $Sub($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(9,239,250)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(105,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/liquidity_math.move:10:9+11
    assume {:print "$track_return(105,1,0):", $t2} $t2 == $t2;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/liquidity_math.move:11:5+1
    assume {:print "$at(9,255,256)"} true;
L1:

    // return $t2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/liquidity_math.move:11:5+1
    assume {:print "$at(9,255,256)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/liquidity_math.move:11:5+1
L2:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/liquidity_math.move:11:5+1
    assume {:print "$at(9,255,256)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct tick::TickInfo at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/tick.move:11:5+1513
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

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:27:5+210
function {:inline} $aa_math_u256_$div_round(num: int, denom: int, round_up: bool): int {
    (var p := (num div denom); (if ((round_up && !$IsEqual'u256'((p * denom), num))) then ((p + 1)) else (p)))
}

// fun math_u256::div_round [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:27:5+210
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
    // trace_local[num]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:27:5+1
    assume {:print "$at(11,618,619)"} true;
    assume {:print "$track_local(107,3,0):", $t0} $t0 == $t0;

    // trace_local[denom]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:27:5+1
    assume {:print "$track_local(107,3,1):", $t1} $t1 == $t1;

    // trace_local[round_up]($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:27:5+1
    assume {:print "$track_local(107,3,2):", $t2} $t2 == $t2;

    // $t5 := /($t0, $t1) on_abort goto L7 with $t6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:28:17+11
    assume {:print "$at(11,703,714)"} true;
    call $t5 := $Div($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(11,703,714)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(107,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_local[$t5]($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:28:17+11
    assume {:print "$track_local(107,3,3):", $t5} $t5 == $t5;

    // if ($t2) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:13+32
    assume {:print "$at(11,728,760)"} true;
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:27+1
L1:

    // $t7 := *($t5, $t1) on_abort goto L7 with $t6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:26+11
    assume {:print "$at(11,741,752)"} true;
    call $t7 := $MulU256($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(11,741,752)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(107,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t8 := !=($t7, $t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:25+20
    $t8 := !$IsEqual'u256'($t7, $t0);

    // $t2 := $t8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:25+20
    $t2 := $t8;

    // trace_local[round_up]($t8) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:25+20
    assume {:print "$track_local(107,3,2):", $t8} $t8 == $t8;

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:9+98
L5:

    // if ($t2) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:9+98
    assume {:print "$at(11,724,822)"} true;
    if ($t2) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:30:13+1
    assume {:print "$at(11,776,777)"} true;
L3:

    // $t9 := 1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:30:17+1
    assume {:print "$at(11,780,781)"} true;
    $t9 := 1;
    assume $IsValid'u256'($t9);

    // $t10 := +($t5, $t9) on_abort goto L7 with $t6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:30:13+5
    call $t10 := $AddU256($t5, $t9);
    if ($abort_flag) {
        assume {:print "$at(11,776,781)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(107,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t4 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:30:13+5
    $t4 := $t10;

    // trace_local[$t8]($t10) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:30:13+5
    assume {:print "$track_local(107,3,4):", $t10} $t10 == $t10;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:9+98
    assume {:print "$at(11,724,822)"} true;
L4:

    // trace_return[0]($t4) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:9+98
    assume {:print "$at(11,724,822)"} true;
    assume {:print "$track_return(107,3,0):", $t4} $t4 == $t4;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:9+98
    goto L6;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:32:13+1
    assume {:print "$at(11,811,812)"} true;
L2:

    // $t4 := $t5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:32:13+1
    assume {:print "$at(11,811,812)"} true;
    $t4 := $t5;

    // trace_local[$t8]($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:32:13+1
    assume {:print "$track_local(107,3,4):", $t5} $t5 == $t5;

    // goto L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:32:13+1
    goto L4;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:13+32
    assume {:print "$at(11,728,760)"} true;
L0:

    // $t11 := false at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:13+32
    assume {:print "$at(11,728,760)"} true;
    $t11 := false;
    assume $IsValid'bool'($t11);

    // $t2 := $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:13+32
    $t2 := $t11;

    // trace_local[round_up]($t11) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:13+32
    assume {:print "$track_local(107,3,2):", $t11} $t11 == $t11;

    // goto L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:29:13+32
    goto L5;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:34:5+1
    assume {:print "$at(11,827,828)"} true;
L6:

    // return $t4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:34:5+1
    assume {:print "$at(11,827,828)"} true;
    $ret0 := $t4;
    return;

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:34:5+1
L7:

    // abort($t6) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/math_u256.move:34:5+1
    assume {:print "$at(11,827,828)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:28:5+97
function {:inline} $aa_full_math_u128_$full_mul(num1: int, num2: int): int {
    (num1 * num2)
}

// fun full_math_u128::full_mul [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:28:5+97
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
    // trace_local[num1]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:28:5+1
    assume {:print "$at(4,885,886)"} true;
    assume {:print "$track_local(109,0,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:28:5+1
    assume {:print "$track_local(109,0,1):", $t1} $t1 == $t1;

    // $t2 := (u256)($t0) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:29:9+14
    assume {:print "$at(4,945,959)"} true;
    call $t2 := $CastU256($t0);
    if ($abort_flag) {
        assume {:print "$at(4,945,959)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(109,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := (u256)($t1) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:29:26+14
    call $t4 := $CastU256($t1);
    if ($abort_flag) {
        assume {:print "$at(4,962,976)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(109,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t5 := *($t2, $t4) on_abort goto L2 with $t3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:29:9+31
    call $t5 := $MulU256($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(4,945,976)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(109,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t5) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:29:9+31
    assume {:print "$track_return(109,0,0):", $t5} $t5 == $t5;

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:30:5+1
    assume {:print "$at(4,981,982)"} true;
L1:

    // return $t5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:30:5+1
    assume {:print "$at(4,981,982)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:30:5+1
L2:

    // abort($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/full_math_u128.move:30:5+1
    assume {:print "$at(4,981,982)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:56:5+1090
function {:inline} $aa_swap_math_$get_delta_a(sqrt_price_0: int, sqrt_price_1: int, liquidity: int, round_up: bool): int {
    (var sqrt_price_diff := (if ((sqrt_price_0 > sqrt_price_1)) then ((sqrt_price_0 - sqrt_price_1)) else ((sqrt_price_1 - sqrt_price_0))); (var quotient := (if (($IsEqual'u128'(sqrt_price_diff, 0) || $IsEqual'u128'(liquidity, 0))) then (0) else ((var temp := $aa_full_math_u128_$full_mul(liquidity, sqrt_price_diff); (var overflowing := (if ((temp > 115792089237316195417293883273301227089434195242432897623355228563449095127040)) then (true) else (false)); (var numberator := (if ((temp > 115792089237316195417293883273301227089434195242432897623355228563449095127040)) then (0) else ($shlU256(temp, 64))); (var denominator := $aa_full_math_u128_$full_mul(sqrt_price_0, sqrt_price_1); $aa_math_u256_$div_round(numberator, denominator, round_up))))))); quotient))
}

// spec fun at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:90:5+859
function {:inline} $aa_swap_math_$get_delta_b(sqrt_price_0: int, sqrt_price_1: int, liquidity: int, round_up: bool): int {
    (var sqrt_price_diff := (if ((sqrt_price_0 > sqrt_price_1)) then ((sqrt_price_0 - sqrt_price_1)) else ((sqrt_price_1 - sqrt_price_0))); (var reproduct := (if (($IsEqual'u128'(sqrt_price_diff, 0) || $IsEqual'u128'(liquidity, 0))) then (0) else ((var product := $aa_full_math_u128_$full_mul(liquidity, sqrt_price_diff); (var should_round_up := (round_up && $Gt'Bv256'($And'Bv256'($int2bv.256(product), 18446744073709551615bv256), 0bv256)); (if (should_round_up) then (($shr(product, 64) + 1)) else ($shr(product, 64))))))); reproduct))
}

// fun swap_math::get_delta_a [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:56:5+1090
procedure {:inline 1} $aa_swap_math_get_delta_a(_$t0: int, _$t1: int, _$t2: int, _$t3: bool) returns ($ret0: int)
{
    // declare local variables
    var $t4: int;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: bool;
    var $t15: bool;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: bool;
    var $t20: int;
    var $t21: bool;
    var $t22: int;
    var $t23: int;
    var $t24: int;
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t28: int;
    var $t29: bool;
    var $t30: int;
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
    // trace_local[sqrt_price_0]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:56:5+1
    assume {:print "$at(12,1691,1692)"} true;
    assume {:print "$track_local(110,3,0):", $t0} $t0 == $t0;

    // trace_local[sqrt_price_1]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:56:5+1
    assume {:print "$track_local(110,3,1):", $t1} $t1 == $t1;

    // trace_local[liquidity]($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:56:5+1
    assume {:print "$track_local(110,3,2):", $t2} $t2 == $t2;

    // trace_local[round_up]($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:56:5+1
    assume {:print "$track_local(110,3,3):", $t3} $t3 == $t3;

    // $t10 := >($t0, $t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:62:35+27
    assume {:print "$at(12,1866,1893)"} true;
    call $t10 := $Gt($t0, $t1);

    // if ($t10) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:62:31+141
    if ($t10) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:63:13+12
    assume {:print "$at(12,1909,1921)"} true;
L1:

    // $t11 := -($t0, $t1) on_abort goto L15 with $t12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:63:13+27
    assume {:print "$at(12,1909,1936)"} true;
    call $t11 := $Sub($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(12,1909,1936)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(110,3):", $t12} $t12 == $t12;
        goto L15;
    }

    // $t4 := $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:63:13+27
    $t4 := $t11;

    // trace_local[$t7]($t11) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:63:13+27
    assume {:print "$track_local(110,3,4):", $t11} $t11 == $t11;

    // label L13 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:28+15
    assume {:print "$at(12,2032,2047)"} true;
L13:

    // $t13 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:47+1
    assume {:print "$at(12,2051,2052)"} true;
    $t13 := 0;
    assume $IsValid'u128'($t13);

    // $t14 := ==($t4, $t13) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:28+20
    $t14 := $IsEqual'u128'($t4, $t13);

    // if ($t14) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:28+38
    if ($t14) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:28+38
L3:

    // $t15 := true at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:28+38
    assume {:print "$at(12,2032,2070)"} true;
    $t15 := true;
    assume $IsValid'bool'($t15);

    // $t5 := $t15 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:28+38
    $t5 := $t15;

    // trace_local[$t6]($t15) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:28+38
    assume {:print "$track_local(110,3,5):", $t15} $t15 == $t15;

    // label L12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:24+729
L12:

    // if ($t5) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:24+729
    assume {:print "$at(12,2028,2757)"} true;
    if ($t5) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:68:12+1
    assume {:print "$at(12,2085,2086)"} true;
L5:

    // $t16 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:68:12+1
    assume {:print "$at(12,2085,2086)"} true;
    $t16 := 0;
    assume $IsValid'u64'($t16);

    // $t6 := $t16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:68:12+1
    $t6 := $t16;

    // trace_local[quotient]($t16) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:68:12+1
    assume {:print "$track_local(110,3,6):", $t16} $t16 == $t16;

    // label L10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:87:9+8
    assume {:print "$at(12,2767,2775)"} true;
L10:

    // trace_return[0]($t6) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:87:9+8
    assume {:print "$at(12,2767,2775)"} true;
    assume {:print "$track_return(110,3,0):", $t6} $t6 == $t6;

    // goto L14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:87:9+8
    goto L14;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:70:49+9
    assume {:print "$at(12,2152,2161)"} true;
L4:

    // $t17 := full_math_u128::full_mul($t2, $t4) on_abort goto L15 with $t12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:70:24+52
    assume {:print "$at(12,2127,2179)"} true;
    call $t17 := $aa_full_math_u128_full_mul($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(12,2127,2179)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(110,3):", $t12} $t12 == $t12;
        goto L15;
    }

    // trace_local[temp]($t17) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:70:24+52
    assume {:print "$track_local(110,3,7):", $t17} $t17 == $t17;

    // $t18 := 115792089237316195417293883273301227089434195242432897623355228563449095127040 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:71:42+27
    assume {:print "$at(12,2222,2249)"} true;
    $t18 := 115792089237316195417293883273301227089434195242432897623355228563449095127040;
    assume $IsValid'u256'($t18);

    // $t19 := >($t17, $t18) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:71:35+34
    call $t19 := $Gt($t17, $t18);

    // if ($t19) goto L7 else goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:71:31+119
    if ($t19) { goto L7; } else { goto L6; }

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:76:35+4
    assume {:print "$at(12,2366,2370)"} true;
L7:

    // $t20 := 115792089237316195417293883273301227089434195242432897623355228563449095127040 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:76:42+27
    assume {:print "$at(12,2373,2400)"} true;
    $t20 := 115792089237316195417293883273301227089434195242432897623355228563449095127040;
    assume $IsValid'u256'($t20);

    // $t21 := >($t17, $t20) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:76:35+34
    call $t21 := $Gt($t17, $t20);

    // if ($t21) goto L9 else goto L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:76:31+123
    if ($t21) { goto L9; } else { goto L8; }

    // label L9 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:77:17+1
    assume {:print "$at(12,2420,2421)"} true;
L9:

    // $t22 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:77:17+1
    assume {:print "$at(12,2420,2421)"} true;
    $t22 := 0;
    assume $IsValid'u256'($t22);

    // $t8 := $t22 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:77:17+1
    $t8 := $t22;

    // trace_local[$t21]($t22) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:77:17+1
    assume {:print "$track_local(110,3,8):", $t22} $t22 == $t22;

    // label L11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:84:56+12
    assume {:print "$at(12,2644,2656)"} true;
L11:

    // $t23 := full_math_u128::full_mul($t0, $t1) on_abort goto L15 with $t12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:84:31+52
    assume {:print "$at(12,2619,2671)"} true;
    call $t23 := $aa_full_math_u128_full_mul($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(12,2619,2671)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(110,3):", $t12} $t12 == $t12;
        goto L15;
    }

    // trace_local[$t22]($t23) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:84:31+52
    assume {:print "$track_local(110,3,9):", $t23} $t23 == $t23;

    // $t24 := math_u256::div_round($t8, $t23, $t3) on_abort goto L15 with $t12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:85:13+55
    assume {:print "$at(12,2685,2740)"} true;
    call $t24 := $aa_math_u256_div_round($t8, $t23, $t3);
    if ($abort_flag) {
        assume {:print "$at(12,2685,2740)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(110,3):", $t12} $t12 == $t12;
        goto L15;
    }

    // $t25 := (u64)($t24) on_abort goto L15 with $t12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:85:13+62
    call $t25 := $CastU64($t24);
    if ($abort_flag) {
        assume {:print "$at(12,2685,2747)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(110,3):", $t12} $t12 == $t12;
        goto L15;
    }

    // $t6 := $t25 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:85:13+62
    $t6 := $t25;

    // trace_local[quotient]($t25) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:85:13+62
    assume {:print "$track_local(110,3,6):", $t25} $t25 == $t25;

    // goto L10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:85:13+62
    goto L10;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:79:18+4
    assume {:print "$at(12,2460,2464)"} true;
L8:

    // $t26 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:79:26+2
    assume {:print "$at(12,2468,2470)"} true;
    $t26 := 64;
    assume $IsValid'u8'($t26);

    // $t27 := <<($t17, $t26) on_abort goto L15 with $t12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:79:17+12
    call $t27 := $ShlU256($t17, $t26);
    if ($abort_flag) {
        assume {:print "$at(12,2459,2471)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(110,3):", $t12} $t12 == $t12;
        goto L15;
    }

    // $t8 := $t27 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:79:17+12
    $t8 := $t27;

    // trace_local[$t21]($t27) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:79:17+12
    assume {:print "$track_local(110,3,8):", $t27} $t27 == $t27;

    // goto L11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:79:17+12
    goto L11;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:74:17+5
    assume {:print "$at(12,2311,2316)"} true;
L6:

    // goto L7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:74:17+5
    assume {:print "$at(12,2311,2316)"} true;
    goto L7;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:52+9
    assume {:print "$at(12,2056,2065)"} true;
L2:

    // $t28 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:65+1
    assume {:print "$at(12,2069,2070)"} true;
    $t28 := 0;
    assume $IsValid'u128'($t28);

    // $t29 := ==($t2, $t28) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:52+14
    $t29 := $IsEqual'u128'($t2, $t28);

    // $t5 := $t29 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:52+14
    $t5 := $t29;

    // trace_local[$t6]($t29) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:52+14
    assume {:print "$track_local(110,3,5):", $t29} $t29 == $t29;

    // goto L12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:67:52+14
    goto L12;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:65:13+12
    assume {:print "$at(12,1966,1978)"} true;
L0:

    // $t30 := -($t1, $t0) on_abort goto L15 with $t12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:65:13+27
    assume {:print "$at(12,1966,1993)"} true;
    call $t30 := $Sub($t1, $t0);
    if ($abort_flag) {
        assume {:print "$at(12,1966,1993)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(110,3):", $t12} $t12 == $t12;
        goto L15;
    }

    // $t4 := $t30 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:65:13+27
    $t4 := $t30;

    // trace_local[$t7]($t30) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:65:13+27
    assume {:print "$track_local(110,3,4):", $t30} $t30 == $t30;

    // goto L13 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:65:13+27
    goto L13;

    // label L14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:88:5+1
    assume {:print "$at(12,2780,2781)"} true;
L14:

    // return $t6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:88:5+1
    assume {:print "$at(12,2780,2781)"} true;
    $ret0 := $t6;
    return;

    // label L15 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:88:5+1
L15:

    // abort($t12) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:88:5+1
    assume {:print "$at(12,2780,2781)"} true;
    $abort_code := $t12;
    $abort_flag := true;
    return;

}

// fun swap_math::get_delta_b [baseline] at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:90:5+859
procedure {:inline 1} $aa_swap_math_get_delta_b(_$t0: int, _$t1: int, _$t2: int, _$t3: bool) returns ($ret0: int)
{
    // declare local variables
    var $t4: int;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: bool;
    var $t14: bool;
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
    // trace_local[sqrt_price_0]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:90:5+1
    assume {:print "$at(12,2787,2788)"} true;
    assume {:print "$track_local(110,4,0):", $t0} $t0 == $t0;

    // trace_local[sqrt_price_1]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:90:5+1
    assume {:print "$track_local(110,4,1):", $t1} $t1 == $t1;

    // trace_local[liquidity]($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:90:5+1
    assume {:print "$track_local(110,4,2):", $t2} $t2 == $t2;

    // trace_local[round_up]($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:90:5+1
    assume {:print "$track_local(110,4,3):", $t3} $t3 == $t3;

    // $t9 := >($t0, $t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:97:35+27
    assume {:print "$at(12,2963,2990)"} true;
    call $t9 := $Gt($t0, $t1);

    // if ($t9) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:97:31+141
    if ($t9) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:98:13+12
    assume {:print "$at(12,3006,3018)"} true;
L1:

    // $t10 := -($t0, $t1) on_abort goto L15 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:98:13+27
    assume {:print "$at(12,3006,3033)"} true;
    call $t10 := $Sub($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(12,3006,3033)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,4):", $t11} $t11 == $t11;
        goto L15;
    }

    // $t4 := $t10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:98:13+27
    $t4 := $t10;

    // trace_local[$t7]($t10) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:98:13+27
    assume {:print "$track_local(110,4,4):", $t10} $t10 == $t10;

    // label L13 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:29+15
    assume {:print "$at(12,3130,3145)"} true;
L13:

    // $t12 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:48+1
    assume {:print "$at(12,3149,3150)"} true;
    $t12 := 0;
    assume $IsValid'u128'($t12);

    // $t13 := ==($t4, $t12) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:29+20
    $t13 := $IsEqual'u128'($t4, $t12);

    // if ($t13) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:29+38
    if ($t13) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:29+38
L3:

    // $t14 := true at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:29+38
    assume {:print "$at(12,3130,3168)"} true;
    $t14 := true;
    assume $IsValid'bool'($t14);

    // $t5 := $t14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:29+38
    $t5 := $t14;

    // trace_local[$t6]($t14) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:29+38
    assume {:print "$track_local(110,4,5):", $t14} $t14 == $t14;

    // label L12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:25+495
L12:

    // if ($t5) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:25+495
    assume {:print "$at(12,3126,3621)"} true;
    if ($t5) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:103:14+1
    assume {:print "$at(12,3185,3186)"} true;
L5:

    // $t15 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:103:14+1
    assume {:print "$at(12,3185,3186)"} true;
    $t15 := 0;
    assume $IsValid'u64'($t15);

    // $t6 := $t15 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:103:14+1
    $t6 := $t15;

    // trace_local[reproduct]($t15) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:103:14+1
    assume {:print "$track_local(110,4,6):", $t15} $t15 == $t15;

    // label L10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:114:9+9
    assume {:print "$at(12,3631,3640)"} true;
L10:

    // trace_return[0]($t6) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:114:9+9
    assume {:print "$at(12,3631,3640)"} true;
    assume {:print "$track_return(110,4,0):", $t6} $t6 == $t6;

    // goto L14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:114:9+9
    goto L14;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:106:52+9
    assume {:print "$at(12,3352,3361)"} true;
L4:

    // $t16 := full_math_u128::full_mul($t2, $t4) on_abort goto L15 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:106:27+52
    assume {:print "$at(12,3327,3379)"} true;
    call $t16 := $aa_full_math_u128_full_mul($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(12,3327,3379)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,4):", $t11} $t11 == $t11;
        goto L15;
    }

    // trace_local[product]($t16) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:106:27+52
    assume {:print "$track_local(110,4,7):", $t16} $t16 == $t16;

    // if ($t3) goto L7 else goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:35+41
    assume {:print "$at(12,3415,3456)"} true;
    if ($t3) { goto L7; } else { goto L6; }

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:51+7
L7:

    // $t17 := 18446744073709551615 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:61+9
    assume {:print "$at(12,3441,3450)"} true;
    $t17 := 18446744073709551615;
    assume $IsValid'u256'($t17);

    // $t18 := &($t16, $t17) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:50+21
    call $t18 := $AndBv256($int2bv.256($t16), $int2bv.256($t17));

    // $t19 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:74+1
    $t19 := 0bv256;
    assume $IsValid'bv256'($t19);

    // $t20 := >($t18, $t19) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:49+27
    call $t20 := $GtBv256($t18, $t19);

    // $t8 := $t20 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:49+27
    $t8 := $t20;

    // trace_local[should_round_up]($t20) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:49+27
    assume {:print "$track_local(110,4,8):", $t20} $t20 == $t20;

    // label L11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:108:13+141
    assume {:print "$at(12,3470,3611)"} true;
L11:

    // if ($t8) goto L9 else goto L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:108:13+141
    assume {:print "$at(12,3470,3611)"} true;
    if ($t8) { goto L9; } else { goto L8; }

    // label L9 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:109:19+7
    assume {:print "$at(12,3511,3518)"} true;
L9:

    // $t21 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:109:30+2
    assume {:print "$at(12,3522,3524)"} true;
    $t21 := 64;
    assume $IsValid'u8'($t21);

    // $t22 := >>($t16, $t21) on_abort goto L15 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:109:18+15
    call $t22 := $ShrU256($t16, $t21);
    if ($abort_flag) {
        assume {:print "$at(12,3510,3525)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,4):", $t11} $t11 == $t11;
        goto L15;
    }

    // $t23 := 1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:109:36+1
    $t23 := 1;
    assume $IsValid'u256'($t23);

    // $t24 := +($t22, $t23) on_abort goto L15 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:109:17+21
    call $t24 := $AddU256($t22, $t23);
    if ($abort_flag) {
        assume {:print "$at(12,3509,3530)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,4):", $t11} $t11 == $t11;
        goto L15;
    }

    // $t25 := (u64)($t24) on_abort goto L15 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:109:17+28
    call $t25 := $CastU64($t24);
    if ($abort_flag) {
        assume {:print "$at(12,3509,3537)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,4):", $t11} $t11 == $t11;
        goto L15;
    }

    // $t6 := $t25 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:109:17+28
    $t6 := $t25;

    // trace_local[reproduct]($t25) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:109:17+28
    assume {:print "$track_local(110,4,6):", $t25} $t25 == $t25;

    // goto L10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:109:17+28
    goto L10;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:111:18+7
    assume {:print "$at(12,3576,3583)"} true;
L8:

    // $t26 := 64 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:111:29+2
    assume {:print "$at(12,3587,3589)"} true;
    $t26 := 64;
    assume $IsValid'u8'($t26);

    // $t27 := >>($t16, $t26) on_abort goto L15 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:111:17+15
    call $t27 := $ShrU256($t16, $t26);
    if ($abort_flag) {
        assume {:print "$at(12,3575,3590)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,4):", $t11} $t11 == $t11;
        goto L15;
    }

    // $t28 := (u64)($t27) on_abort goto L15 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:111:17+22
    call $t28 := $CastU64($t27);
    if ($abort_flag) {
        assume {:print "$at(12,3575,3597)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,4):", $t11} $t11 == $t11;
        goto L15;
    }

    // $t6 := $t28 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:111:17+22
    $t6 := $t28;

    // trace_local[reproduct]($t28) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:111:17+22
    assume {:print "$track_local(110,4,6):", $t28} $t28 == $t28;

    // goto L10 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:111:17+22
    goto L10;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:35+41
    assume {:print "$at(12,3415,3456)"} true;
L6:

    // $t29 := false at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:35+41
    assume {:print "$at(12,3415,3456)"} true;
    $t29 := false;
    assume $IsValid'bool'($t29);

    // $t8 := $t29 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:35+41
    $t8 := $t29;

    // trace_local[should_round_up]($t29) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:35+41
    assume {:print "$track_local(110,4,8):", $t29} $t29 == $t29;

    // goto L11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:107:35+41
    goto L11;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:53+9
    assume {:print "$at(12,3154,3163)"} true;
L2:

    // $t30 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:66+1
    assume {:print "$at(12,3167,3168)"} true;
    $t30 := 0;
    assume $IsValid'u128'($t30);

    // $t31 := ==($t2, $t30) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:53+14
    $t31 := $IsEqual'u128'($t2, $t30);

    // $t5 := $t31 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:53+14
    $t5 := $t31;

    // trace_local[$t6]($t31) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:53+14
    assume {:print "$track_local(110,4,5):", $t31} $t31 == $t31;

    // goto L12 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:102:53+14
    goto L12;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:100:13+12
    assume {:print "$at(12,3063,3075)"} true;
L0:

    // $t32 := -($t1, $t0) on_abort goto L15 with $t11 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:100:13+27
    assume {:print "$at(12,3063,3090)"} true;
    call $t32 := $Sub($t1, $t0);
    if ($abort_flag) {
        assume {:print "$at(12,3063,3090)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(110,4):", $t11} $t11 == $t11;
        goto L15;
    }

    // $t4 := $t32 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:100:13+27
    $t4 := $t32;

    // trace_local[$t7]($t32) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:100:13+27
    assume {:print "$track_local(110,4,4):", $t32} $t32 == $t32;

    // goto L13 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:100:13+27
    goto L13;

    // label L14 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:115:5+1
    assume {:print "$at(12,3645,3646)"} true;
L14:

    // return $t6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:115:5+1
    assume {:print "$at(12,3645,3646)"} true;
    $ret0 := $t6;
    return;

    // label L15 at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:115:5+1
L15:

    // abort($t11) at /Users/jackfisher/Desktop/audits/dex-v3/sources/math/swap_math.move:115:5+1
    assume {:print "$at(12,3645,3646)"} true;
    $abort_code := $t11;
    $abort_flag := true;
    return;

}

// struct rewarder::Rewarder at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/rewarder.move:27:5+299
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

// struct rewarder::RewarderManager at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/rewarder.move:21:5+129
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

// struct position_blacklist::PositionBlackList at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/position_blacklist.move:7:5+82
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

// struct lp::LPTokenRefs at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/lp.move:18:5+160
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

// struct pool_v3::LiquidityPoolV3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:65:5+1544
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

// struct pool_v3::ProtocolFees at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:104:5+115
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

// fun pool_v3::dividen_from_pool [verification] at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+3721
procedure {:timeLimit 40} $aa_pool_v3_dividen_from_pool$verify(_$t0: $Mutation ($aa_pool_v3_LiquidityPoolV3), _$t1: $aa_i32_I32, _$t2: $aa_i32_I32, _$t3: int) returns ($ret0: int, $ret1: int, $ret2: int, $ret3: $1_option_Option'$1_fungible_asset_FungibleAsset', $ret4: $1_option_Option'$1_fungible_asset_FungibleAsset', $ret5: $Mutation ($aa_pool_v3_LiquidityPoolV3))
{
    // declare local variables
    var $t4: $1_option_Option'$1_fungible_asset_FungibleAsset';
    var $t5: $1_option_Option'$1_fungible_asset_FungibleAsset';
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: $aa_pool_v3_LiquidityPoolV3;
    var $t13: $1_option_Option'$1_fungible_asset_FungibleAsset';
    var $t14: $1_option_Option'$1_fungible_asset_FungibleAsset';
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: bool;
    var $t19: $aa_i32_I32;
    var $t20: bool;
    var $t21: int;
    var $t22: int;
    var $t23: int;
    var $t24: bool;
    var $t25: int;
    var $t26: $aa_i32_I32;
    var $t27: bool;
    var $t28: int;
    var $t29: int;
    var $t30: bool;
    var $t31: int;
    var $t32: int;
    var $t33: int;
    var $t34: bool;
    var $t35: int;
    var $t36: int;
    var $t37: int;
    var $t38: $Mutation (int);
    var $t39: int;
    var $t40: int;
    var $t41: bool;
    var $t42: int;
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
    // assume And(WellFormed($t0), And(And(And(And(And(And(Or(option::$is_none<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), And(option::$is_some<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), Neq<u64>(option::$borrow<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), 0))), Or(option::$is_none<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), Le(Len<address>(select smart_vector::SmartVector.inline_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$borrow<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))))), Or(And(option::$is_none<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$is_none<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), And(option::$is_some<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$is_some<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))))), Le(Len<0x1::big_vector::BigVector<address>>(select option::Option.vec(select smart_vector::SmartVector.big_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1)), forall $elem: 0x1::big_vector::BigVector<address>: select option::Option.vec(select smart_vector::SmartVector.big_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))): And(And(And(And(And(And(And(And(And(And(And(Neq<u64>(select big_vector::BigVector.bucket_size($elem), 0), Implies(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<u64>(select big_vector::BigVector.end_index($elem), 0))), Implies(Eq<u64>(select big_vector::BigVector.end_index($elem), 0), Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0))), Le(select big_vector::BigVector.end_index($elem), Mul(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), select big_vector::BigVector.bucket_size($elem)))), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), forall i: num: Range(0, Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1)): Eq<num>(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), select big_vector::BigVector.bucket_size($elem)))), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Le(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1))), select big_vector::BigVector.bucket_size($elem)))), forall i: num: Range(0, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), Div(Sub(Add(select big_vector::BigVector.end_index($elem), select big_vector::BigVector.bucket_size($elem)), 1), select big_vector::BigVector.bucket_size($elem)))), Or(And(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<u64>(select big_vector::BigVector.end_index($elem), 0)), And(Neq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<num>(Add(Mul(Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1), select big_vector::BigVector.bucket_size($elem)), Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1)))), select big_vector::BigVector.end_index($elem))))), forall i: u64: TypeDomain<u64>() where Ge(i, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): Not(big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i))), forall i: u64: TypeDomain<u64>() where Lt(i, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Gt(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1))), 0)))), Le(Len<u64>(select option::Option.vec(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1)), Le(Len<u64>(select option::Option.vec(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1))) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+1
    assume {:print "$at(19,59317,59318)"} true;
    assume ($IsValid'$aa_pool_v3_LiquidityPoolV3'($Dereference($t0)) && ((((((($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size) || ($1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size) && !$IsEqual'u64'($1_option_$borrow'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size), 0))) && ($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) || (LenVec($Dereference($t0)->$position_blacklist->$addresses->$inline_vec) <= $1_option_$borrow'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity)))) && (($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) && $1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size)) || ($1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) && $1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size)))) && (LenVec($Dereference($t0)->$position_blacklist->$addresses->$big_vec->$vec) <= 1)) && (var $range_0 := $Dereference($t0)->$position_blacklist->$addresses->$big_vec->$vec; (forall $i_1: int :: InRangeVec($range_0, $i_1) ==> (var $elem := ReadVec($range_0, $i_1);
    ((((((((((((!$IsEqual'u64'($elem->$bucket_size, 0) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) ==> $IsEqual'u64'($elem->$end_index, 0))) && ($IsEqual'u64'($elem->$end_index, 0) ==> $IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0))) && ($elem->$end_index <= ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) * $elem->$bucket_size))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (var $range_2 := $Range(0, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1)); (forall $i_3: int :: $InRange($range_2, $i_3) ==> (var i := $i_3;
    ($IsEqual'num'(LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, i)), $elem->$bucket_size))))))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1))) <= $elem->$bucket_size))) && (var $range_4 := $Range(0, $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)); (forall $i_5: int :: $InRange($range_4, $i_5) ==> (var i := $i_5;
    ($1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))))) && $IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), ((($elem->$end_index + $elem->$bucket_size) - 1) div $elem->$bucket_size))) && (($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) && $IsEqual'u64'($elem->$end_index, 0)) || (!$IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) && $IsEqual'num'(((($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1) * $elem->$bucket_size) + LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1)))), $elem->$end_index)))) && (forall i: int :: $IsValid'u64'(i) ==> ((i >= $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)))  ==> (!$1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))) && (forall i: int :: $IsValid'u64'(i) ==> ((i < $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)))  ==> ($1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1))) > 0)))))))) && (LenVec($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity->$vec) <= 1)) && (LenVec($Dereference($t0)->$position_blacklist->$addresses->$bucket_size->$vec) <= 1)));

    // assume WellFormed($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+1
    assume $IsValid'$aa_i32_I32'($t1);

    // assume WellFormed($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+1
    assume $IsValid'$aa_i32_I32'($t2);

    // assume WellFormed($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+1
    assume $IsValid'u128'($t3);

    // assume Identical($t8, swap_math::$get_delta_a(tick_math::$get_sqrt_price_at_tick($t1), tick_math::$get_sqrt_price_at_tick($t2), $t3, false)) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1613:9+220
    assume {:print "$at(19,63128,63348)"} true;
    assume ($t8 == $aa_swap_math_$get_delta_a($aa_tick_math_$get_sqrt_price_at_tick($t1), $aa_tick_math_$get_sqrt_price_at_tick($t2), $t3, false));

    // assume Identical($t9, swap_math::$get_delta_a(select pool_v3::LiquidityPoolV3.sqrt_price<0xaa::pool_v3::LiquidityPoolV3>($t0), tick_math::$get_sqrt_price_at_tick($t2), $t3, false)) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1619:9+193
    assume {:print "$at(19,63357,63550)"} true;
    assume ($t9 == $aa_swap_math_$get_delta_a($Dereference($t0)->$sqrt_price, $aa_tick_math_$get_sqrt_price_at_tick($t2), $t3, false));

    // assume Identical($t10, swap_math::$get_delta_b(tick_math::$get_sqrt_price_at_tick($t1), select pool_v3::LiquidityPoolV3.sqrt_price<0xaa::pool_v3::LiquidityPoolV3>($t0), $t3, false)) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1625:9+193
    assume {:print "$at(19,63559,63752)"} true;
    assume ($t10 == $aa_swap_math_$get_delta_b($aa_tick_math_$get_sqrt_price_at_tick($t1), $Dereference($t0)->$sqrt_price, $t3, false));

    // assume Identical($t11, swap_math::$get_delta_b(tick_math::$get_sqrt_price_at_tick($t1), tick_math::$get_sqrt_price_at_tick($t2), $t3, false)) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1631:9+220
    assume {:print "$at(19,63761,63981)"} true;
    assume ($t11 == $aa_swap_math_$get_delta_b($aa_tick_math_$get_sqrt_price_at_tick($t1), $aa_tick_math_$get_sqrt_price_at_tick($t2), $t3, false));

    // $t12 := read_ref($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+1
    assume {:print "$at(19,59317,59318)"} true;
    $t12 := $Dereference($t0);

    // trace_local[pool]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+1
    $temp_0'$aa_pool_v3_LiquidityPoolV3' := $Dereference($t0);
    assume {:print "$track_local(117,34,0):", $temp_0'$aa_pool_v3_LiquidityPoolV3'} $temp_0'$aa_pool_v3_LiquidityPoolV3' == $temp_0'$aa_pool_v3_LiquidityPoolV3';

    // trace_local[tick_lower]($t1) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+1
    assume {:print "$track_local(117,34,1):", $t1} $t1 == $t1;

    // trace_local[tick_upper]($t2) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+1
    assume {:print "$track_local(117,34,2):", $t2} $t2 == $t2;

    // trace_local[liquidity_delta]($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1534:5+1
    assume {:print "$track_local(117,34,3):", $t3} $t3 == $t3;

    // $t13 := opaque begin: option::none<0x1::fungible_asset::FungibleAsset>() at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1540:24+29
    assume {:print "$at(19,59552,59581)"} true;

    // assume And(WellFormed($t13), Le(Len<0x1::fungible_asset::FungibleAsset>(select option::Option.vec($t13)), 1)) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1540:24+29
    assume ($IsValid'$1_option_Option'$1_fungible_asset_FungibleAsset''($t13) && (LenVec($t13->$vec) <= 1));

    // assume Eq<0x1::option::Option<0x1::fungible_asset::FungibleAsset>>($t13, option::spec_none<0x1::fungible_asset::FungibleAsset>()) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1540:24+29
    assume $IsEqual'$1_option_Option'$1_fungible_asset_FungibleAsset''($t13, $1_option_spec_none'$1_fungible_asset_FungibleAsset'());

    // $t13 := opaque end: option::none<0x1::fungible_asset::FungibleAsset>() at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1540:24+29

    // trace_local[fa_a_opt]($t13) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1540:24+29
    assume {:print "$track_local(117,34,4):", $t13} $t13 == $t13;

    // $t14 := opaque begin: option::none<0x1::fungible_asset::FungibleAsset>() at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1541:24+29
    assume {:print "$at(19,59606,59635)"} true;

    // assume And(WellFormed($t14), Le(Len<0x1::fungible_asset::FungibleAsset>(select option::Option.vec($t14)), 1)) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1541:24+29
    assume ($IsValid'$1_option_Option'$1_fungible_asset_FungibleAsset''($t14) && (LenVec($t14->$vec) <= 1));

    // assume Eq<0x1::option::Option<0x1::fungible_asset::FungibleAsset>>($t14, option::spec_none<0x1::fungible_asset::FungibleAsset>()) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1541:24+29
    assume $IsEqual'$1_option_Option'$1_fungible_asset_FungibleAsset''($t14, $1_option_spec_none'$1_fungible_asset_FungibleAsset'());

    // $t14 := opaque end: option::none<0x1::fungible_asset::FungibleAsset>() at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1541:24+29

    // trace_local[fa_b_opt]($t14) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1541:24+29
    assume {:print "$track_local(117,34,5):", $t14} $t14 == $t14;

    // $t15 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1542:37+1
    assume {:print "$at(19,59673,59674)"} true;
    $t15 := 0;
    assume $IsValid'u64'($t15);

    // $t6 := $t15 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1542:37+1
    $t6 := $t15;

    // trace_local[$t13]($t15) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1542:37+1
    assume {:print "$track_local(117,34,6):", $t15} $t15 == $t15;

    // $t16 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1542:40+1
    $t16 := 0;
    assume $IsValid'u64'($t16);

    // $t7 := $t16 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1542:40+1
    $t7 := $t16;

    // trace_local[$t14]($t16) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1542:40+1
    assume {:print "$track_local(117,34,7):", $t16} $t16 == $t16;

    // $t17 := 0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1543:32+1
    assume {:print "$at(19,59711,59712)"} true;
    $t17 := 0;
    assume $IsValid'u128'($t17);

    // $t18 := !=($t3, $t17) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1543:13+20
    $t18 := !$IsEqual'u128'($t3, $t17);

    // if ($t18) goto L1 else goto L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1543:9+3277
    if ($t18) { goto L1; } else { goto L0; }

    // label L1 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1544:25+9
    assume {:print "$at(19,59740,59749)"} true;
L1:

    // $t19 := get_field<0xaa::pool_v3::LiquidityPoolV3>.tick($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1544:25+9
    assume {:print "$at(19,59740,59749)"} true;
    $t19 := $Dereference($t0)->$tick;

    // $t20 := i32::lt($t19, $t1) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1544:17+30
    call $t20 := $aa_i32_lt($t19, $t1);
    if ($abort_flag) {
        assume {:print "$at(19,59732,59762)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // if ($t20) goto L3 else goto L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1544:13+3226
    if ($t20) { goto L3; } else { goto L2; }

    // label L3 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1544:49+759
L3:

    // drop($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1544:49+759
    assume {:print "$at(19,59764,60523)"} true;

    // $t22 := tick_math::get_sqrt_price_at_tick($t1) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1548:21+45
    assume {:print "$at(19,60066,60111)"} true;
    call $t22 := $aa_tick_math_get_sqrt_price_at_tick($t1);
    if ($abort_flag) {
        assume {:print "$at(19,60066,60111)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t23 := tick_math::get_sqrt_price_at_tick($t2) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1549:21+45
    assume {:print "$at(19,60133,60178)"} true;
    call $t23 := $aa_tick_math_get_sqrt_price_at_tick($t2);
    if ($abort_flag) {
        assume {:print "$at(19,60133,60178)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t24 := false at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1551:21+5
    assume {:print "$at(19,60237,60242)"} true;
    $t24 := false;
    assume $IsValid'bool'($t24);

    // $t25 := swap_math::get_delta_a($t22, $t23, $t3, $t24) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1547:28+238
    assume {:print "$at(19,60022,60260)"} true;
    call $t25 := $aa_swap_math_get_delta_a($t22, $t23, $t3, $t24);
    if ($abort_flag) {
        assume {:print "$at(19,60022,60260)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t6 := $t25 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1547:17+249
    $t6 := $t25;

    // trace_local[$t13]($t25) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1547:17+249
    assume {:print "$track_local(117,34,6):", $t25} $t25 == $t25;

    // label L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1608:10+15
    assume {:print "$at(19,62976,62991)"} true;
L6:

    // trace_return[0]($t3) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1539:71+3511
    assume {:print "$at(19,59527,63038)"} true;
    assume {:print "$track_return(117,34,0):", $t3} $t3 == $t3;

    // trace_return[1]($t6) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1539:71+3511
    assume {:print "$track_return(117,34,1):", $t6} $t6 == $t6;

    // trace_return[2]($t7) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1539:71+3511
    assume {:print "$track_return(117,34,2):", $t7} $t7 == $t7;

    // trace_return[3]($t13) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1539:71+3511
    assume {:print "$track_return(117,34,3):", $t13} $t13 == $t13;

    // trace_return[4]($t14) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1539:71+3511
    assume {:print "$track_return(117,34,4):", $t14} $t14 == $t14;

    // trace_local[pool]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1539:71+3511
    $temp_0'$aa_pool_v3_LiquidityPoolV3' := $Dereference($t0);
    assume {:print "$track_local(117,34,0):", $temp_0'$aa_pool_v3_LiquidityPoolV3'} $temp_0'$aa_pool_v3_LiquidityPoolV3' == $temp_0'$aa_pool_v3_LiquidityPoolV3';

    // assert Or(option::$is_none<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), And(option::$is_some<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), Neq<u64>(option::$borrow<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), 0))) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:5:9+121
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:5:9+121
    assume {:print "$at(79,118,239)"} true;
    assert {:msg "assert_failed(79,118,239): data invariant does not hold"}
      ($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size) || ($1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size) && !$IsEqual'u64'($1_option_$borrow'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size), 0)));

    // assert Or(option::$is_none<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), Le(Len<address>(select smart_vector::SmartVector.inline_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$borrow<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))))) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:8:9+111
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:8:9+111
    assume {:print "$at(79,319,430)"} true;
    assert {:msg "assert_failed(79,319,430): data invariant does not hold"}
      ($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) || (LenVec($Dereference($t0)->$position_blacklist->$addresses->$inline_vec) <= $1_option_$borrow'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity)));

    // assert Or(And(option::$is_none<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$is_none<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), And(option::$is_some<u64>(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))), option::$is_some<u64>(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))))) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:11:9+159
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/smart_vector.spec.move:11:9+159
    assume {:print "$at(79,538,697)"} true;
    assert {:msg "assert_failed(79,538,697): data invariant does not hold"}
      (($1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) && $1_option_$is_none'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size)) || ($1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity) && $1_option_$is_some'u64'($Dereference($t0)->$position_blacklist->$addresses->$bucket_size)));

    // assert Le(Len<0x1::big_vector::BigVector<address>>(select option::Option.vec(select smart_vector::SmartVector.big_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    assume {:print "$at(38,530,554)"} true;
    assert {:msg "assert_failed(38,530,554): data invariant does not hold"}
      (LenVec($Dereference($t0)->$position_blacklist->$addresses->$big_vec->$vec) <= 1);

    // assert forall $elem: 0x1::big_vector::BigVector<address>: select option::Option.vec(select smart_vector::SmartVector.big_vec(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0)))): And(And(And(And(And(And(And(And(And(And(And(Neq<u64>(select big_vector::BigVector.bucket_size($elem), 0), Implies(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<u64>(select big_vector::BigVector.end_index($elem), 0))), Implies(Eq<u64>(select big_vector::BigVector.end_index($elem), 0), Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0))), Le(select big_vector::BigVector.end_index($elem), Mul(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), select big_vector::BigVector.bucket_size($elem)))), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), forall i: num: Range(0, Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1)): Eq<num>(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), select big_vector::BigVector.bucket_size($elem)))), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Le(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1))), select big_vector::BigVector.bucket_size($elem)))), forall i: num: Range(0, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), Div(Sub(Add(select big_vector::BigVector.end_index($elem), select big_vector::BigVector.bucket_size($elem)), 1), select big_vector::BigVector.bucket_size($elem)))), Or(And(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<u64>(select big_vector::BigVector.end_index($elem), 0)), And(Neq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Eq<num>(Add(Mul(Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1), select big_vector::BigVector.bucket_size($elem)), Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1)))), select big_vector::BigVector.end_index($elem))))), forall i: u64: TypeDomain<u64>() where Ge(i, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): Not(big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i))), forall i: u64: TypeDomain<u64>() where Lt(i, big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem))): big_vector::spec_table_contains<u64, vector<address>>(select big_vector::BigVector.buckets($elem), i)), Or(Eq<u64>(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 0), Gt(Len<address>(table_with_length::spec_get<u64, vector<address>>(select big_vector::BigVector.buckets($elem), Sub(big_vector::spec_table_len<u64, vector<address>>(select big_vector::BigVector.buckets($elem)), 1))), 0))) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/big_vector.spec.move:7:9+27
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/data_structures/big_vector.spec.move:7:9+27
    assume {:print "$at(75,132,159)"} true;
    assert {:msg "assert_failed(75,132,159): data invariant does not hold"}
      (var $range_0 := $Dereference($t0)->$position_blacklist->$addresses->$big_vec->$vec; (forall $i_1: int :: InRangeVec($range_0, $i_1) ==> (var $elem := ReadVec($range_0, $i_1);
    ((((((((((((!$IsEqual'u64'($elem->$bucket_size, 0) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) ==> $IsEqual'u64'($elem->$end_index, 0))) && ($IsEqual'u64'($elem->$end_index, 0) ==> $IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0))) && ($elem->$end_index <= ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) * $elem->$bucket_size))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (var $range_2 := $Range(0, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1)); (forall $i_3: int :: $InRange($range_2, $i_3) ==> (var i := $i_3;
    ($IsEqual'num'(LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, i)), $elem->$bucket_size))))))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1))) <= $elem->$bucket_size))) && (var $range_4 := $Range(0, $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)); (forall $i_5: int :: $InRange($range_4, $i_5) ==> (var i := $i_5;
    ($1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))))) && $IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), ((($elem->$end_index + $elem->$bucket_size) - 1) div $elem->$bucket_size))) && (($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) && $IsEqual'u64'($elem->$end_index, 0)) || (!$IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) && $IsEqual'num'(((($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1) * $elem->$bucket_size) + LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1)))), $elem->$end_index)))) && (forall i: int :: $IsValid'u64'(i) ==> ((i >= $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)))  ==> (!$1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))) && (forall i: int :: $IsValid'u64'(i) ==> ((i < $1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets)))  ==> ($1_big_vector_spec_table_contains'u64_vec'address''($elem->$buckets, i)))) && ($IsEqual'u64'($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets), 0) || (LenVec($1_table_with_length_spec_get'u64_vec'address''($elem->$buckets, ($1_big_vector_spec_table_len'u64_vec'address''($elem->$buckets) - 1))) > 0)))))));

    // assert Le(Len<u64>(select option::Option.vec(select smart_vector::SmartVector.inline_capacity(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    assume {:print "$at(38,530,554)"} true;
    assert {:msg "assert_failed(38,530,554): data invariant does not hold"}
      (LenVec($Dereference($t0)->$position_blacklist->$addresses->$inline_capacity->$vec) <= 1);

    // assert Le(Len<u64>(select option::Option.vec(select smart_vector::SmartVector.bucket_size(select position_blacklist::PositionBlackList.addresses(select pool_v3::LiquidityPoolV3.position_blacklist($t0))))), 1) at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    // data invariant at /Users/jackfisher/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:13:9+24
    assert {:msg "assert_failed(38,530,554): data invariant does not hold"}
      (LenVec($Dereference($t0)->$position_blacklist->$addresses->$bucket_size->$vec) <= 1);

    // goto L7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1539:71+3511
    assume {:print "$at(19,59527,63038)"} true;
    goto L7;

    // label L2 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1557:32+9
    assume {:print "$at(19,60541,60550)"} true;
L2:

    // $t26 := get_field<0xaa::pool_v3::LiquidityPoolV3>.tick($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1557:32+9
    assume {:print "$at(19,60541,60550)"} true;
    $t26 := $Dereference($t0)->$tick;

    // $t27 := i32::lt($t26, $t2) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1557:24+30
    call $t27 := $aa_i32_lt($t26, $t2);
    if ($abort_flag) {
        assume {:print "$at(19,60533,60563)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // if ($t27) goto L5 else goto L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1557:20+2425
    if ($t27) { goto L5; } else { goto L4; }

    // label L5 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1573:21+15
    assume {:print "$at(19,61252,61267)"} true;
L5:

    // $t28 := get_field<0xaa::pool_v3::LiquidityPoolV3>.sqrt_price($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1573:21+15
    assume {:print "$at(19,61252,61267)"} true;
    $t28 := $Dereference($t0)->$sqrt_price;

    // $t29 := tick_math::get_sqrt_price_at_tick($t2) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1574:21+45
    assume {:print "$at(19,61289,61334)"} true;
    call $t29 := $aa_tick_math_get_sqrt_price_at_tick($t2);
    if ($abort_flag) {
        assume {:print "$at(19,61289,61334)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t30 := false at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1576:21+5
    assume {:print "$at(19,61393,61398)"} true;
    $t30 := false;
    assume $IsValid'bool'($t30);

    // $t31 := swap_math::get_delta_a($t28, $t29, $t3, $t30) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1572:28+208
    assume {:print "$at(19,61208,61416)"} true;
    call $t31 := $aa_swap_math_get_delta_a($t28, $t29, $t3, $t30);
    if ($abort_flag) {
        assume {:print "$at(19,61208,61416)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t6 := $t31 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1572:17+219
    $t6 := $t31;

    // trace_local[$t13]($t31) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1572:17+219
    assume {:print "$track_local(117,34,6):", $t31} $t31 == $t31;

    // $t32 := tick_math::get_sqrt_price_at_tick($t1) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1583:21+45
    assume {:print "$at(19,61737,61782)"} true;
    call $t32 := $aa_tick_math_get_sqrt_price_at_tick($t1);
    if ($abort_flag) {
        assume {:print "$at(19,61737,61782)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t33 := get_field<0xaa::pool_v3::LiquidityPoolV3>.sqrt_price($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1584:21+15
    assume {:print "$at(19,61804,61819)"} true;
    $t33 := $Dereference($t0)->$sqrt_price;

    // $t34 := false at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1586:21+5
    assume {:print "$at(19,61878,61883)"} true;
    $t34 := false;
    assume $IsValid'bool'($t34);

    // $t35 := swap_math::get_delta_b($t32, $t33, $t3, $t34) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1582:28+208
    assume {:print "$at(19,61693,61901)"} true;
    call $t35 := $aa_swap_math_get_delta_b($t32, $t33, $t3, $t34);
    if ($abort_flag) {
        assume {:print "$at(19,61693,61901)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t7 := $t35 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1582:17+219
    $t7 := $t35;

    // trace_local[$t14]($t35) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1582:17+219
    assume {:print "$track_local(117,34,7):", $t35} $t35 == $t35;

    // $t36 := get_field<0xaa::pool_v3::LiquidityPoolV3>.liquidity($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1592:60+14
    assume {:print "$at(19,62142,62156)"} true;
    $t36 := $Dereference($t0)->$liquidity;

    // $t37 := liquidity_math::sub_delta($t36, $t3) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1592:34+58
    call $t37 := $aa_liquidity_math_sub_delta($t36, $t3);
    if ($abort_flag) {
        assume {:print "$at(19,62116,62174)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t38 := borrow_field<0xaa::pool_v3::LiquidityPoolV3>.liquidity($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1592:17+14
    $t38 := $ChildMutation($t0, 5, $Dereference($t0)->$liquidity);

    // write_ref($t38, $t37) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1592:17+75
    $t38 := $UpdateMutation($t38, $t37);

    // write_back[Reference($t0).liquidity (u128)]($t38) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1592:17+75
    $t0 := $UpdateMutation($t0, $Update'$aa_pool_v3_LiquidityPoolV3'_liquidity($Dereference($t0), $Dereference($t38)));

    // trace_local[pool]($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1592:17+75
    $temp_0'$aa_pool_v3_LiquidityPoolV3' := $Dereference($t0);
    assume {:print "$track_local(117,34,0):", $temp_0'$aa_pool_v3_LiquidityPoolV3'} $temp_0'$aa_pool_v3_LiquidityPoolV3' == $temp_0'$aa_pool_v3_LiquidityPoolV3';

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1557:56+1624
    assume {:print "$at(19,60565,62189)"} true;
    goto L6;

    // label L4 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1593:20+759
    assume {:print "$at(19,62195,62954)"} true;
L4:

    // drop($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1593:20+759
    assume {:print "$at(19,62195,62954)"} true;

    // $t39 := tick_math::get_sqrt_price_at_tick($t1) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1597:21+45
    assume {:print "$at(19,62497,62542)"} true;
    call $t39 := $aa_tick_math_get_sqrt_price_at_tick($t1);
    if ($abort_flag) {
        assume {:print "$at(19,62497,62542)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t40 := tick_math::get_sqrt_price_at_tick($t2) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1598:21+45
    assume {:print "$at(19,62564,62609)"} true;
    call $t40 := $aa_tick_math_get_sqrt_price_at_tick($t2);
    if ($abort_flag) {
        assume {:print "$at(19,62564,62609)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t41 := false at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1600:21+5
    assume {:print "$at(19,62668,62673)"} true;
    $t41 := false;
    assume $IsValid'bool'($t41);

    // $t42 := swap_math::get_delta_b($t39, $t40, $t3, $t41) on_abort goto L8 with $t21 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1596:28+238
    assume {:print "$at(19,62453,62691)"} true;
    call $t42 := $aa_swap_math_get_delta_b($t39, $t40, $t3, $t41);
    if ($abort_flag) {
        assume {:print "$at(19,62453,62691)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(117,34):", $t21} $t21 == $t21;
        goto L8;
    }

    // $t7 := $t42 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1596:17+249
    $t7 := $t42;

    // trace_local[$t14]($t42) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1596:17+249
    assume {:print "$track_local(117,34,7):", $t42} $t42 == $t42;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1596:17+249
    goto L6;

    // label L0 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1543:9+3277
    assume {:print "$at(19,59688,62965)"} true;
L0:

    // drop($t0) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1543:9+3277
    assume {:print "$at(19,59688,62965)"} true;

    // goto L6 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1543:9+3277
    goto L6;

    // label L7 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1609:5+1
    assume {:print "$at(19,63037,63038)"} true;
L7:

    // assert Implies(And(Neq<u128>($t3, 0), Lt(i32::$as_u32(select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t0)), i32::$as_u32($t1))), And(Eq<u64>($t6, $t8), Eq<u64>($t7, 0))) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1638:9+168
    assume {:print "$at(19,64047,64215)"} true;
    assert {:msg "assert_failed(19,64047,64215): post-condition does not hold"}
      ((!$IsEqual'u128'($t3, 0) && $Lt'Bv32'($aa_i32_$as_u32($Dereference($t0)->$tick), $aa_i32_$as_u32($t1))) ==> ($IsEqual'u64'($t6, $t8) && $IsEqual'u64'($t7, 0)));

    // assert Implies(And(And(Neq<u128>($t3, 0), Ge(i32::$as_u32(select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t0)), i32::$as_u32($t1))), Lt(i32::$as_u32(select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t0)), i32::$as_u32($t2))), And(And(Eq<u64>($t6, $t9), Eq<u64>($t7, $t10)), Eq<u128>(select pool_v3::LiquidityPoolV3.liquidity<0xaa::pool_v3::LiquidityPoolV3>($t12), Sub(select pool_v3::LiquidityPoolV3.liquidity<0xaa::pool_v3::LiquidityPoolV3>($t0), $t3)))) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1643:9+324
    assume {:print "$at(19,64276,64600)"} true;
    assert {:msg "assert_failed(19,64276,64600): post-condition does not hold"}
      (((!$IsEqual'u128'($t3, 0) && $Ge'Bv32'($aa_i32_$as_u32($Dereference($t0)->$tick), $aa_i32_$as_u32($t1))) && $Lt'Bv32'($aa_i32_$as_u32($Dereference($t0)->$tick), $aa_i32_$as_u32($t2))) ==> (($IsEqual'u64'($t6, $t9) && $IsEqual'u64'($t7, $t10)) && $IsEqual'u128'($t12->$liquidity, ($Dereference($t0)->$liquidity - $t3))));

    // assert Implies(And(Neq<u128>($t3, 0), Ge(i32::$as_u32(select pool_v3::LiquidityPoolV3.tick<0xaa::pool_v3::LiquidityPoolV3>($t0)), i32::$as_u32($t2))), And(Eq<u64>($t6, 0), Eq<u64>($t7, $t11))) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1650:9+169
    assume {:print "$at(19,64666,64835)"} true;
    assert {:msg "assert_failed(19,64666,64835): post-condition does not hold"}
      ((!$IsEqual'u128'($t3, 0) && $Ge'Bv32'($aa_i32_$as_u32($Dereference($t0)->$tick), $aa_i32_$as_u32($t2))) ==> ($IsEqual'u64'($t6, 0) && $IsEqual'u64'($t7, $t11)));

    // return ($t3, $t6, $t7, $t13, $t14) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1650:9+169
    $ret0 := $t3;
    $ret1 := $t6;
    $ret2 := $t7;
    $ret3 := $t13;
    $ret4 := $t14;
    $ret5 := $t0;
    return;

    // label L8 at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1609:5+1
    assume {:print "$at(19,63037,63038)"} true;
L8:

    // abort($t21) at /Users/jackfisher/Desktop/audits/dex-v3/sources/v3/pool_v3.move:1609:5+1
    assume {:print "$at(19,63037,63038)"} true;
    $abort_code := $t21;
    $abort_flag := true;
    return;

}
