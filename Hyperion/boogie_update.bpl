
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Type conversion functions for bv128 <-> int conversions
function {:inline} $IntToBv128(i: int): bv128 { $int2bv.128(i) }
function {:inline} $Bv128ToInt(b: bv128): int { $bv2int.128(b) }

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

function $Arbitrary_value_of'$1_permissioned_signer_GrantedPermissionHandles'(): $1_permissioned_signer_GrantedPermissionHandles;

function $Arbitrary_value_of'$aa_i128_I128'(): $aa_i128_I128;

function $Arbitrary_value_of'$aa_i32_I32'(): $aa_i32_I32;

function $Arbitrary_value_of'$aa_tick_TickInfo'(): $aa_tick_TickInfo;

function $Arbitrary_value_of'$aa_tick_TickUpdatedEvent'(): $aa_tick_TickUpdatedEvent;

function $Arbitrary_value_of'vec'address''(): Vec (int);

function $Arbitrary_value_of'vec'u128''(): Vec (int);

function $Arbitrary_value_of'vec'u8''(): Vec (int);

function $Arbitrary_value_of'bool'(): bool;

function $Arbitrary_value_of'address'(): int;

function $Arbitrary_value_of'u128'(): int;

function $Arbitrary_value_of'u256'(): int;

function $Arbitrary_value_of'u32'(): int;

function $Arbitrary_value_of'u64'(): int;

function $Arbitrary_value_of'u8'(): int;

function $Arbitrary_value_of'vec'bv128''(): Vec (bv128);

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

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'bool'(b1), $1_from_bcs_deserializable'bool'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u8>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u8'(b1), $1_from_bcs_deserializable'u8'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u32>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u32'(b1), $1_from_bcs_deserializable'u32'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u64'(b1), $1_from_bcs_deserializable'u64'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u128'(b1), $1_from_bcs_deserializable'u128'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u256'(b1), $1_from_bcs_deserializable'u256'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'address'(b1), $1_from_bcs_deserializable'address'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u8''(b1), $1_from_bcs_deserializable'vec'u8''(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u128''(b1), $1_from_bcs_deserializable'vec'u128''(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'address''(b1), $1_from_bcs_deserializable'vec'address''(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0x1::permissioned_signer::GrantedPermissionHandles>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_permissioned_signer_GrantedPermissionHandles'(b1), $1_from_bcs_deserializable'$1_permissioned_signer_GrantedPermissionHandles'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::i32::I32>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_i32_I32'(b1), $1_from_bcs_deserializable'$aa_i32_I32'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::i128::I128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_i128_I128'(b1), $1_from_bcs_deserializable'$aa_i128_I128'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::tick::TickInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_tick_TickInfo'(b1), $1_from_bcs_deserializable'$aa_tick_TickInfo'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <0xaa::tick::TickUpdatedEvent>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$aa_tick_TickUpdatedEvent'(b1), $1_from_bcs_deserializable'$aa_tick_TickUpdatedEvent'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'#0'(b1), $1_from_bcs_deserializable'#0'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserialize'bool'(b1), $1_from_bcs_deserialize'bool'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u8>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u8'($1_from_bcs_deserialize'u8'(b1), $1_from_bcs_deserialize'u8'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u32>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u32'($1_from_bcs_deserialize'u32'(b1), $1_from_bcs_deserialize'u32'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u64'($1_from_bcs_deserialize'u64'(b1), $1_from_bcs_deserialize'u64'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u128'($1_from_bcs_deserialize'u128'(b1), $1_from_bcs_deserialize'u128'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u256'($1_from_bcs_deserialize'u256'(b1), $1_from_bcs_deserialize'u256'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'address'($1_from_bcs_deserialize'address'(b1), $1_from_bcs_deserialize'address'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u128''($1_from_bcs_deserialize'vec'u128''(b1), $1_from_bcs_deserialize'vec'u128''(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'address''($1_from_bcs_deserialize'vec'address''(b1), $1_from_bcs_deserialize'vec'address''(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0x1::permissioned_signer::GrantedPermissionHandles>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_permissioned_signer_GrantedPermissionHandles'($1_from_bcs_deserialize'$1_permissioned_signer_GrantedPermissionHandles'(b1), $1_from_bcs_deserialize'$1_permissioned_signer_GrantedPermissionHandles'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::i32::I32>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_i32_I32'($1_from_bcs_deserialize'$aa_i32_I32'(b1), $1_from_bcs_deserialize'$aa_i32_I32'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::i128::I128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_i128_I128'($1_from_bcs_deserialize'$aa_i128_I128'(b1), $1_from_bcs_deserialize'$aa_i128_I128'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::tick::TickInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_tick_TickInfo'($1_from_bcs_deserialize'$aa_tick_TickInfo'(b1), $1_from_bcs_deserialize'$aa_tick_TickInfo'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <0xaa::tick::TickUpdatedEvent>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$aa_tick_TickUpdatedEvent'($1_from_bcs_deserialize'$aa_tick_TickUpdatedEvent'(b1), $1_from_bcs_deserialize'$aa_tick_TickUpdatedEvent'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/permissioned_signer.spec.move:5:9+288
axiom (forall a: $1_permissioned_signer_GrantedPermissionHandles :: $IsValid'$1_permissioned_signer_GrantedPermissionHandles'(a) ==> ((var $range_0 := $Range(0, LenVec(a->$active_handles)); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var i := $i_1;
((var $range_2 := $Range(0, LenVec(a->$active_handles)); (forall $i_3: int :: $InRange($range_2, $i_3) ==> (var j := $i_3;
((!$IsEqual'num'(i, j) ==> !$IsEqual'address'(ReadVec(a->$active_handles, i), ReadVec(a->$active_handles, j)))))))))))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:8:9+113
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_keccak256(b1), $1_aptos_hash_spec_keccak256(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:13:9+129
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_sha2_512_internal(b1), $1_aptos_hash_spec_sha2_512_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:18:9+129
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_sha3_512_internal(b1), $1_aptos_hash_spec_sha3_512_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:23:9+131
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_ripemd160_internal(b1), $1_aptos_hash_spec_ripemd160_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:28:9+135
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_blake2b_256_internal(b1), $1_aptos_hash_spec_blake2b_256_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// fun error::invalid_argument [baseline] at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:3+76
procedure {:inline 1} $1_error_invalid_argument(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[r]($t0) at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:3+1
    assume {:print "$at(42,3082,3083)"} true;
    assume {:print "$track_local(5,4,0):", $t0} $t0 == $t0;

    // $t1 := 1 at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:57+16
    $t1 := 1;
    assume $IsValid'u64'($t1);

    // assume Identical($t2, Shl($t1, 16)) at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:69:5+29
    assume {:print "$at(42,2844,2873)"} true;
    assume ($t2 == $shlU64($t1, 16));

    // $t3 := opaque begin: error::canonical($t1, $t0) at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30
    assume {:print "$at(42,3126,3156)"} true;

    // assume WellFormed($t3) at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30
    assume $IsValid'u64'($t3);

    // assume Eq<u64>($t3, $t1) at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30
    assume $IsEqual'u64'($t3, $t1);

    // $t3 := opaque end: error::canonical($t1, $t0) at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30

    // trace_return[0]($t3) at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30
    assume {:print "$track_return(5,4,0):", $t3} $t3 == $t3;

    // label L1 at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:78+1
L1:

    // return $t3 at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:78+1
    assume {:print "$at(42,3157,3158)"} true;
    $ret0 := $t3;
    return;

}

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'bool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'bool'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u8'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u8'(bytes);
$IsValid'u8'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u32'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u32'(bytes);
$IsValid'u32'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u64'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u64'(bytes);
$IsValid'u64'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u128'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u128'(bytes);
$IsValid'u128'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u256'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u256'(bytes);
$IsValid'u256'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'address'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'address'(bytes);
$IsValid'address'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u8''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u8''(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u128''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u128''(bytes);
$IsValid'vec'u128''($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'address''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'address''(bytes);
$IsValid'vec'address''($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_permissioned_signer_GrantedPermissionHandles'(bytes: Vec (int)): $1_permissioned_signer_GrantedPermissionHandles;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_permissioned_signer_GrantedPermissionHandles'(bytes);
$IsValid'$1_permissioned_signer_GrantedPermissionHandles'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_i32_I32'(bytes: Vec (int)): $aa_i32_I32;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_i32_I32'(bytes);
$IsValid'$aa_i32_I32'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_i128_I128'(bytes: Vec (int)): $aa_i128_I128;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_i128_I128'(bytes);
$IsValid'$aa_i128_I128'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_tick_TickInfo'(bytes: Vec (int)): $aa_tick_TickInfo;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_tick_TickInfo'(bytes);
$IsValid'$aa_tick_TickInfo'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$aa_tick_TickUpdatedEvent'(bytes: Vec (int)): $aa_tick_TickUpdatedEvent;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$aa_tick_TickUpdatedEvent'(bytes);
$IsValid'$aa_tick_TickUpdatedEvent'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'#0'(bytes: Vec (int)): #0;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'#0'(bytes);
$IsValid'#0'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'bool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'bool'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u8'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u8'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u32'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u32'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u64'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u64'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u128'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u128'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u256'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u256'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'address'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'address'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u8''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u8''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u128''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u128''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'address''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'address''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_permissioned_signer_GrantedPermissionHandles'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_permissioned_signer_GrantedPermissionHandles'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_i32_I32'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_i32_I32'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_i128_I128'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_i128_I128'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_tick_TickInfo'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_tick_TickInfo'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$aa_tick_TickUpdatedEvent'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$aa_tick_TickUpdatedEvent'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'#0'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'#0'(bytes);
$IsValid'bool'($$res)));

// struct permissioned_signer::GrantedPermissionHandles at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/sources/permissioned_signer.move:64:5+188
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

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:7:9+50
function  $1_aptos_hash_spec_keccak256(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_keccak256(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:12:9+58
function  $1_aptos_hash_spec_sha2_512_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_sha2_512_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:17:9+58
function  $1_aptos_hash_spec_sha3_512_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_sha3_512_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:22:9+59
function  $1_aptos_hash_spec_ripemd160_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_ripemd160_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/mikb/.move/https___github_com_aptos-labs_aptos-framework_git_mainnet/aptos-framework/../aptos-stdlib/sources/hash.spec.move:27:9+61
function  $1_aptos_hash_spec_blake2b_256_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_blake2b_256_internal(bytes);
$IsValid'vec'u8''($$res)));

// struct i32::I32 at ./sources/math/i32.move:11:5+58
datatype $aa_i32_I32 {
    $aa_i32_I32($bits: int)
}
function {:inline} $Update'$aa_i32_I32'_bits(s: $aa_i32_I32, x: int): $aa_i32_I32 {
    $aa_i32_I32(x)
}
function $IsValid'$aa_i32_I32'(s: $aa_i32_I32): bool {
    $IsValid'u32'(s->$bits)
}
function {:inline} $IsEqual'$aa_i32_I32'(s1: $aa_i32_I32, s2: $aa_i32_I32): bool {
    s1 == s2
}

// fun i32::cmp [baseline] at ./sources/math/i32.move:179:5+299
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
    // trace_local[num1]($t0) at ./sources/math/i32.move:179:5+1
    assume {:print "$at(7,3947,3948)"} true;
    assume {:print "$track_local(98,2,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at ./sources/math/i32.move:179:5+1
    assume {:print "$track_local(98,2,1):", $t1} $t1 == $t1;

    // $t2 := get_field<0xaa::i32::I32>.bits($t0) at ./sources/math/i32.move:180:13+9
    assume {:print "$at(7,4002,4011)"} true;
    $t2 := $t0->$bits;

    // $t3 := get_field<0xaa::i32::I32>.bits($t1) at ./sources/math/i32.move:180:26+9
    $t3 := $t1->$bits;

    // $t4 := ==($t2, $t3) at ./sources/math/i32.move:180:13+22
    $t4 := $IsEqual'u32'($t2, $t3);

    // if ($t4) goto L1 else goto L0 at ./sources/math/i32.move:180:9+37
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at ./sources/math/i32.move:180:44+2
L1:

    // $t5 := 1 at ./sources/math/i32.move:180:44+2
    assume {:print "$at(7,4033,4035)"} true;
    $t5 := 1;
    assume $IsValid'u8'($t5);

    // trace_return[0]($t5) at ./sources/math/i32.move:180:37+9
    assume {:print "$track_return(98,2,0):", $t5} $t5 == $t5;

    // $t6 := move($t5) at ./sources/math/i32.move:180:37+9
    $t6 := $t5;

    // goto L8 at ./sources/math/i32.move:180:37+9
    goto L8;

    // label L0 at ./sources/math/i32.move:181:13+10
    assume {:print "$at(7,4049,4059)"} true;
L0:

    // $t7 := i32::sign($t0) on_abort goto L9 with $t8 at ./sources/math/i32.move:181:13+10
    assume {:print "$at(7,4049,4059)"} true;
    call $t7 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,4049,4059)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t9 := i32::sign($t1) on_abort goto L9 with $t8 at ./sources/math/i32.move:181:26+10
    call $t9 := $aa_i32_sign($t1);
    if ($abort_flag) {
        assume {:print "$at(7,4062,4072)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t10 := >($t7, $t9) at ./sources/math/i32.move:181:13+23
    call $t10 := $Gt($t7, $t9);

    // if ($t10) goto L3 else goto L2 at ./sources/math/i32.move:181:9+38
    if ($t10) { goto L3; } else { goto L2; }

    // label L3 at ./sources/math/i32.move:181:45+2
L3:

    // $t11 := 0 at ./sources/math/i32.move:181:45+2
    assume {:print "$at(7,4081,4083)"} true;
    $t11 := 0;
    assume $IsValid'u8'($t11);

    // trace_return[0]($t11) at ./sources/math/i32.move:181:38+9
    assume {:print "$track_return(98,2,0):", $t11} $t11 == $t11;

    // $t6 := move($t11) at ./sources/math/i32.move:181:38+9
    $t6 := $t11;

    // goto L8 at ./sources/math/i32.move:181:38+9
    goto L8;

    // label L2 at ./sources/math/i32.move:182:13+10
    assume {:print "$at(7,4097,4107)"} true;
L2:

    // $t12 := i32::sign($t0) on_abort goto L9 with $t8 at ./sources/math/i32.move:182:13+10
    assume {:print "$at(7,4097,4107)"} true;
    call $t12 := $aa_i32_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(7,4097,4107)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t13 := i32::sign($t1) on_abort goto L9 with $t8 at ./sources/math/i32.move:182:26+10
    call $t13 := $aa_i32_sign($t1);
    if ($abort_flag) {
        assume {:print "$at(7,4110,4120)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(98,2):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t14 := <($t12, $t13) at ./sources/math/i32.move:182:13+23
    call $t14 := $Lt($t12, $t13);

    // if ($t14) goto L5 else goto L4 at ./sources/math/i32.move:182:9+38
    if ($t14) { goto L5; } else { goto L4; }

    // label L5 at ./sources/math/i32.move:182:45+2
L5:

    // $t15 := 2 at ./sources/math/i32.move:182:45+2
    assume {:print "$at(7,4129,4131)"} true;
    $t15 := 2;
    assume $IsValid'u8'($t15);

    // trace_return[0]($t15) at ./sources/math/i32.move:182:38+9
    assume {:print "$track_return(98,2,0):", $t15} $t15 == $t15;

    // $t6 := move($t15) at ./sources/math/i32.move:182:38+9
    $t6 := $t15;

    // goto L8 at ./sources/math/i32.move:182:38+9
    goto L8;

    // label L4 at ./sources/math/i32.move:183:13+4
    assume {:print "$at(7,4145,4149)"} true;
L4:

    // $t16 := get_field<0xaa::i32::I32>.bits($t0) at ./sources/math/i32.move:183:13+9
    assume {:print "$at(7,4145,4154)"} true;
    $t16 := $t0->$bits;

    // $t17 := get_field<0xaa::i32::I32>.bits($t1) at ./sources/math/i32.move:183:25+9
    $t17 := $t1->$bits;

    // $t18 := >($t16, $t17) at ./sources/math/i32.move:183:13+21
    call $t18 := $Gt($t16, $t17);

    // if ($t18) goto L7 else goto L6 at ./sources/math/i32.move:183:9+99
    if ($t18) { goto L7; } else { goto L6; }

    // label L7 at ./sources/math/i32.move:184:20+2
    assume {:print "$at(7,4189,4191)"} true;
L7:

    // $t19 := 2 at ./sources/math/i32.move:184:20+2
    assume {:print "$at(7,4189,4191)"} true;
    $t19 := 2;
    assume $IsValid'u8'($t19);

    // trace_return[0]($t19) at ./sources/math/i32.move:184:13+9
    assume {:print "$track_return(98,2,0):", $t19} $t19 == $t19;

    // $t6 := move($t19) at ./sources/math/i32.move:184:13+9
    $t6 := $t19;

    // goto L8 at ./sources/math/i32.move:184:13+9
    goto L8;

    // label L6 at ./sources/math/i32.move:186:20+2
    assume {:print "$at(7,4228,4230)"} true;
L6:

    // $t20 := 0 at ./sources/math/i32.move:186:20+2
    assume {:print "$at(7,4228,4230)"} true;
    $t20 := 0;
    assume $IsValid'u8'($t20);

    // trace_return[0]($t20) at ./sources/math/i32.move:186:13+9
    assume {:print "$track_return(98,2,0):", $t20} $t20 == $t20;

    // $t6 := move($t20) at ./sources/math/i32.move:186:13+9
    $t6 := $t20;

    // label L8 at ./sources/math/i32.move:188:5+1
    assume {:print "$at(7,4245,4246)"} true;
L8:

    // return $t6 at ./sources/math/i32.move:188:5+1
    assume {:print "$at(7,4245,4246)"} true;
    $ret0 := $t6;
    return;

    // label L9 at ./sources/math/i32.move:188:5+1
L9:

    // abort($t8) at ./sources/math/i32.move:188:5+1
    assume {:print "$at(7,4245,4246)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun i32::sign [baseline] at ./sources/math/i32.move:171:5+66
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
    // trace_local[v]($t0) at ./sources/math/i32.move:171:5+1
    assume {:print "$at(7,3809,3810)"} true;
    assume {:print "$track_local(98,8,0):", $t0} $t0 == $t0;

    // $t1 := get_field<0xaa::i32::I32>.bits($t0) at ./sources/math/i32.move:172:11+6
    assume {:print "$at(7,3849,3855)"} true;
    $t1 := $t0->$bits;

    // $t2 := 31 at ./sources/math/i32.move:172:21+2
    $t2 := 31;
    assume $IsValid'u8'($t2);

    // $t3 := >>($t1, $t2) on_abort goto L2 with $t4 at ./sources/math/i32.move:172:10+14
    call $t3 := $ShrU32($t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(7,3848,3862)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(98,8):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := (u8)($t3) on_abort goto L2 with $t4 at ./sources/math/i32.move:172:9+22
    call $t5 := $CastU8($t3);
    if ($abort_flag) {
        assume {:print "$at(7,3847,3869)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(98,8):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t5) at ./sources/math/i32.move:172:9+22
    assume {:print "$track_return(98,8,0):", $t5} $t5 == $t5;

    // label L1 at ./sources/math/i32.move:173:5+1
    assume {:print "$at(7,3874,3875)"} true;
L1:

    // return $t5 at ./sources/math/i32.move:173:5+1
    assume {:print "$at(7,3874,3875)"} true;
    $ret0 := $t5;
    return;

    // label L2 at ./sources/math/i32.move:173:5+1
L2:

    // abort($t4) at ./sources/math/i32.move:173:5+1
    assume {:print "$at(7,3874,3875)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun i32::lte [baseline] at ./sources/math/i32.move:206:5+80
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
    // trace_local[num1]($t0) at ./sources/math/i32.move:206:5+1
    assume {:print "$at(7,4594,4595)"} true;
    assume {:print "$track_local(98,19,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at ./sources/math/i32.move:206:5+1
    assume {:print "$track_local(98,19,1):", $t1} $t1 == $t1;

    // $t2 := i32::cmp($t0, $t1) on_abort goto L2 with $t3 at ./sources/math/i32.move:207:9+15
    assume {:print "$at(7,4647,4662)"} true;
    call $t2 := $aa_i32_cmp($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(7,4647,4662)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(98,19):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := 1 at ./sources/math/i32.move:207:28+2
    $t4 := 1;
    assume $IsValid'u8'($t4);

    // $t5 := <=($t2, $t4) at ./sources/math/i32.move:207:9+21
    call $t5 := $Le($t2, $t4);

    // trace_return[0]($t5) at ./sources/math/i32.move:207:9+21
    assume {:print "$track_return(98,19,0):", $t5} $t5 == $t5;

    // label L1 at ./sources/math/i32.move:208:5+1
    assume {:print "$at(7,4673,4674)"} true;
L1:

    // return $t5 at ./sources/math/i32.move:208:5+1
    assume {:print "$at(7,4673,4674)"} true;
    $ret0 := $t5;
    return;

    // label L2 at ./sources/math/i32.move:208:5+1
L2:

    // abort($t3) at ./sources/math/i32.move:208:5+1
    assume {:print "$at(7,4673,4674)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct i128::I128 at ./sources/math/i128.move:15:5+60
datatype $aa_i128_I128 {
    $aa_i128_I128($bits: bv128)
}
function {:inline} $Update'$aa_i128_I128'_bits(s: $aa_i128_I128, x: bv128): $aa_i128_I128 {
    $aa_i128_I128(x)
}
function $IsValid'$aa_i128_I128'(s: $aa_i128_I128): bool {
    $IsValid'bv128'(s->$bits)
}
function {:inline} $IsEqual'$aa_i128_I128'(s1: $aa_i128_I128, s2: $aa_i128_I128): bool {
    s1 == s2
}

// fun i128::from [baseline] at ./sources/math/i128.move:25:5+153
procedure {:inline 1} $aa_i128_from(_$t0: bv128) returns ($ret0: $aa_i128_I128)
{
    // declare local variables
    var $t1: int;
    var $t2: bool;
    var $t3: $aa_i128_I128;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t0: bv128;
    var $temp_0'$aa_i128_I128': $aa_i128_I128;
    var $temp_0'bv128': bv128;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at ./sources/math/i128.move:25:5+1
    assume {:print "$at(6,459,460)"} true;
    assume {:print "$track_local(100,0,0):", $t0} $t0 == $t0;

    // $t1 := 170141183460469231731687303715884105727 at ./sources/math/i128.move:26:22+11
    assume {:print "$at(6,513,524)"} true;
    $t1 := 170141183460469231731687303715884105727;
    assume $IsValid'u128'($t1);

    // $t2 := <=($t0, $t1) at ./sources/math/i128.move:26:17+16
    call $t2 := $LeBv128($t0, $IntToBv128($t1));

    // if ($t2) goto L1 else goto L0 at ./sources/math/i128.move:26:9+6
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at ./sources/math/i128.move:27:9+36
    assume {:print "$at(6,570,606)"} true;
L1:

    // $t3 := pack 0xaa::i128::I128($t0) at ./sources/math/i128.move:27:9+36
    assume {:print "$at(6,570,606)"} true;
    $t3 := $aa_i128_I128($t0);

    // trace_return[0]($t3) at ./sources/math/i128.move:25:36+122
    assume {:print "$at(6,490,612)"} true;
    assume {:print "$track_return(100,0,0):", $t3} $t3 == $t3;

    // goto L2 at ./sources/math/i128.move:25:36+122
    goto L2;

    // label L0 at ./sources/math/i128.move:26:59+8
    assume {:print "$at(6,550,558)"} true;
L0:

    // $t4 := 0 at ./sources/math/i128.move:26:59+8
    assume {:print "$at(6,550,558)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // $t5 := error::invalid_argument($t4) on_abort goto L3 with $t6 at ./sources/math/i128.move:26:35+33
    call $t5 := $1_error_invalid_argument($t4);
    if ($abort_flag) {
        assume {:print "$at(6,526,559)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(100,0):", $t6} $t6 == $t6;
        goto L3;
    }

    // trace_abort($t5) at ./sources/math/i128.move:26:9+6
    assume {:print "$at(6,500,506)"} true;
    assume {:print "$track_abort(100,0):", $t5} $t5 == $t5;

    // $t6 := move($t5) at ./sources/math/i128.move:26:9+6
    $t6 := $t5;

    // goto L3 at ./sources/math/i128.move:26:9+6
    goto L3;

    // label L2 at ./sources/math/i128.move:30:5+1
    assume {:print "$at(6,611,612)"} true;
L2:

    // return $t3 at ./sources/math/i128.move:30:5+1
    assume {:print "$at(6,611,612)"} true;
    $ret0 := $t3;
    return;

    // label L3 at ./sources/math/i128.move:30:5+1
L3:

    // abort($t6) at ./sources/math/i128.move:30:5+1
    assume {:print "$at(6,611,612)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun i128::add [baseline] at ./sources/math/i128.move:67:5+301
procedure {:inline 1} $aa_i128_add(_$t0: $aa_i128_I128, _$t1: $aa_i128_I128) returns ($ret0: $aa_i128_I128)
{
    // declare local variables
    var $t2: $aa_i128_I128;
    var $t3: $aa_i128_I128;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bv8;
    var $t8: int;
    var $t9: bv8;
    var $t10: bv8;
    var $t11: int;
    var $t12: bv8;
    var $t13: int;
    var $t14: bv8;
    var $t15: bv8;
    var $t16: int;
    var $t17: bv8;
    var $t18: bv8;
    var $t19: bv8;
    var $t20: bool;
    var $t21: int;
    var $t22: int;
    var $t0: $aa_i128_I128;
    var $t1: $aa_i128_I128;
    var $temp_0'$aa_i128_I128': $aa_i128_I128;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[num1]($t0) at ./sources/math/i128.move:67:5+1
    assume {:print "$at(6,1427,1428)"} true;
    assume {:print "$track_local(100,1,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at ./sources/math/i128.move:67:5+1
    assume {:print "$track_local(100,1,1):", $t1} $t1 == $t1;

    // $t3 := i128::wrapping_add($t0, $t1) on_abort goto L3 with $t4 at ./sources/math/i128.move:68:19+24
    assume {:print "$at(6,1492,1516)"} true;
    call $t3 := $aa_i128_wrapping_add($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,1492,1516)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // trace_local[$t4]($t3) at ./sources/math/i128.move:68:19+24
    assume {:print "$track_local(100,1,2):", $t3} $t3 == $t3;

    // $t5 := i128::sign($t0) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:25+10
    assume {:print "$at(6,1542,1552)"} true;
    call $t5 := $aa_i128_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(6,1542,1552)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t6 := i128::sign($t1) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:38+10
    call $t6 := $aa_i128_sign($t1);
    if ($abort_flag) {
        assume {:print "$at(6,1555,1565)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t7 := &($t5, $t6) at ./sources/math/i128.move:69:25+23
    call $t7 := $AndBv8($int2bv.8($t5), $int2bv.8($t6));

    // $t8 := i128::sign($t3) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:58+9
    call $t8 := $aa_i128_sign($t3);
    if ($abort_flag) {
        assume {:print "$at(6,1575,1584)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t9 := i128::u8_neg($t8) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:51+17
    call $t9 := $aa_i128_u8_neg($t8);
    if ($abort_flag) {
        assume {:print "$at(6,1568,1585)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t10 := &($t7, $t9) at ./sources/math/i128.move:69:24+45
    call $t10 := $AndBv8($t7, $t9);

    // $t11 := i128::sign($t0) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:80+10
    call $t11 := $aa_i128_sign($t0);
    if ($abort_flag) {
        assume {:print "$at(6,1597,1607)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t12 := i128::u8_neg($t11) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:73+18
    call $t12 := $aa_i128_u8_neg($t11);
    if ($abort_flag) {
        assume {:print "$at(6,1590,1608)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t13 := i128::sign($t1) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:101+10
    call $t13 := $aa_i128_sign($t1);
    if ($abort_flag) {
        assume {:print "$at(6,1618,1628)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t14 := i128::u8_neg($t13) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:94+18
    call $t14 := $aa_i128_u8_neg($t13);
    if ($abort_flag) {
        assume {:print "$at(6,1611,1629)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t15 := &($t12, $t14) at ./sources/math/i128.move:69:73+39
    call $t15 := $AndBv8($t12, $t14);

    // $t16 := i128::sign($t3) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:115+9
    call $t16 := $aa_i128_sign($t3);
    if ($abort_flag) {
        assume {:print "$at(6,1632,1641)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t17 := &($t15, $t16) at ./sources/math/i128.move:69:72+53
    call $t17 := $AndBv8($t15, $int2bv.8($t16));

    // $t18 := +($t10, $t17) on_abort goto L3 with $t4 at ./sources/math/i128.move:69:24+101
    call $t18 := $AddBv8($t10, $t17);
    if ($abort_flag) {
        assume {:print "$at(6,1541,1642)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t19 := 0 at ./sources/math/i128.move:70:29+1
    assume {:print "$at(6,1672,1673)"} true;
    $t19 := 0bv8;
    assume $IsValid'bv8'($t19);

    // $t20 := ==($t18, $t19) at ./sources/math/i128.move:70:17+13
    $t20 := $IsEqual'bv8'($t18, $t19);

    // if ($t20) goto L1 else goto L0 at ./sources/math/i128.move:70:9+6
    if ($t20) { goto L1; } else { goto L0; }

    // label L1 at ./sources/math/i128.move:71:9+3
    assume {:print "$at(6,1719,1722)"} true;
L1:

    // trace_return[0]($t3) at ./sources/math/i128.move:67:50+256
    assume {:print "$at(6,1472,1728)"} true;
    assume {:print "$track_return(100,1,0):", $t3} $t3 == $t3;

    // goto L2 at ./sources/math/i128.move:67:50+256
    goto L2;

    // label L0 at ./sources/math/i128.move:70:56+8
    assume {:print "$at(6,1699,1707)"} true;
L0:

    // $t21 := 0 at ./sources/math/i128.move:70:56+8
    assume {:print "$at(6,1699,1707)"} true;
    $t21 := 0;
    assume $IsValid'u64'($t21);

    // $t22 := error::invalid_argument($t21) on_abort goto L3 with $t4 at ./sources/math/i128.move:70:32+33
    call $t22 := $1_error_invalid_argument($t21);
    if ($abort_flag) {
        assume {:print "$at(6,1675,1708)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,1):", $t4} $t4 == $t4;
        goto L3;
    }

    // trace_abort($t22) at ./sources/math/i128.move:70:9+6
    assume {:print "$at(6,1652,1658)"} true;
    assume {:print "$track_abort(100,1):", $t22} $t22 == $t22;

    // $t4 := move($t22) at ./sources/math/i128.move:70:9+6
    $t4 := $t22;

    // goto L3 at ./sources/math/i128.move:70:9+6
    goto L3;

    // label L2 at ./sources/math/i128.move:72:5+1
    assume {:print "$at(6,1727,1728)"} true;
L2:

    // return $t3 at ./sources/math/i128.move:72:5+1
    assume {:print "$at(6,1727,1728)"} true;
    $ret0 := $t3;
    return;

    // label L3 at ./sources/math/i128.move:72:5+1
L3:

    // abort($t4) at ./sources/math/i128.move:72:5+1
    assume {:print "$at(6,1727,1728)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun i128::sub [baseline] at ./sources/math/i128.move:87:5+180
procedure {:inline 1} $aa_i128_sub(_$t0: $aa_i128_I128, _$t1: $aa_i128_I128) returns ($ret0: $aa_i128_I128)
{
    // declare local variables
    var $t2: $aa_i128_I128;
    var $t3: bv128;
    var $t4: bv128;
    var $t5: int;
    var $t6: $aa_i128_I128;
    var $t7: int;
    var $t8: $aa_i128_I128;
    var $t9: $aa_i128_I128;
    var $t10: $aa_i128_I128;
    var $t0: $aa_i128_I128;
    var $t1: $aa_i128_I128;
    var $temp_0'$aa_i128_I128': $aa_i128_I128;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[num1]($t0) at ./sources/math/i128.move:87:5+1
    assume {:print "$at(6,2215,2216)"} true;
    assume {:print "$track_local(100,3,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at ./sources/math/i128.move:87:5+1
    assume {:print "$track_local(100,3,1):", $t1} $t1 == $t1;

    // $t3 := get_field<0xaa::i128::I128>.bits($t1) at ./sources/math/i128.move:89:28+9
    assume {:print "$at(6,2331,2340)"} true;
    $t3 := $t1->$bits;

    // $t4 := i128::u128_neg($t3) on_abort goto L2 with $t5 at ./sources/math/i128.move:89:19+19
    call $t4 := $aa_i128_u128_neg($t3);
    if ($abort_flag) {
        assume {:print "$at(6,2322,2341)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(100,3):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t6 := pack 0xaa::i128::I128($t4) at ./sources/math/i128.move:88:36+54
    assume {:print "$at(6,2297,2351)"} true;
    $t6 := $aa_i128_I128($t4);

    // $t7 := 1 at ./sources/math/i128.move:90:17+1
    assume {:print "$at(6,2358,2359)"} true;
    $t7 := 1;
    assume $IsValid'u128'($t7);

    // $t8 := i128::from($t7) on_abort goto L2 with $t5 at ./sources/math/i128.move:90:12+7
    call $t8 := $aa_i128_from($IntToBv128($t7));
    if ($abort_flag) {
        assume {:print "$at(6,2353,2360)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(100,3):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t9 := i128::wrapping_add($t6, $t8) on_abort goto L2 with $t5 at ./sources/math/i128.move:88:23+77
    assume {:print "$at(6,2284,2361)"} true;
    call $t9 := $aa_i128_wrapping_add($t6, $t8);
    if ($abort_flag) {
        assume {:print "$at(6,2284,2361)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(100,3):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[$t4]($t9) at ./sources/math/i128.move:88:23+77
    assume {:print "$track_local(100,3,2):", $t9} $t9 == $t9;

    // $t10 := i128::add($t0, $t9) on_abort goto L2 with $t5 at ./sources/math/i128.move:91:9+18
    assume {:print "$at(6,2371,2389)"} true;
    call $t10 := $aa_i128_add($t0, $t9);
    if ($abort_flag) {
        assume {:print "$at(6,2371,2389)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(100,3):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_return[0]($t10) at ./sources/math/i128.move:91:9+18
    assume {:print "$track_return(100,3,0):", $t10} $t10 == $t10;

    // label L1 at ./sources/math/i128.move:92:5+1
    assume {:print "$at(6,2394,2395)"} true;
L1:

    // return $t10 at ./sources/math/i128.move:92:5+1
    assume {:print "$at(6,2394,2395)"} true;
    $ret0 := $t10;
    return;

    // label L2 at ./sources/math/i128.move:92:5+1
L2:

    // abort($t5) at ./sources/math/i128.move:92:5+1
    assume {:print "$at(6,2394,2395)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun i128::sign [baseline] at ./sources/math/i128.move:179:5+68
procedure {:inline 1} $aa_i128_sign(_$t0: $aa_i128_I128) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: $aa_i128_I128;
    var $temp_0'$aa_i128_I128': $aa_i128_I128;
    var $temp_0'u8': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at ./sources/math/i128.move:179:5+1
    assume {:print "$at(6,4626,4627)"} true;
    assume {:print "$track_local(100,9,0):", $t0} $t0 == $t0;

    // $t1 := get_field<0xaa::i128::I128>.bits($t0) at ./sources/math/i128.move:180:11+6
    assume {:print "$at(6,4667,4673)"} true;
    $t1 := $Bv128ToInt($t0->$bits);

    // $t2 := 127 at ./sources/math/i128.move:180:21+3
    $t2 := 127;
    assume $IsValid'u8'($t2);

    // $t3 := >>($t1, $t2) on_abort goto L2 with $t4 at ./sources/math/i128.move:180:10+15
    call $t3 := $ShrU128($t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(6,4666,4681)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,9):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := (u8)($t3) on_abort goto L2 with $t4 at ./sources/math/i128.move:180:9+23
    call $t5 := $CastU8($t3);
    if ($abort_flag) {
        assume {:print "$at(6,4665,4688)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(100,9):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t5) at ./sources/math/i128.move:180:9+23
    assume {:print "$track_return(100,9,0):", $t5} $t5 == $t5;

    // label L1 at ./sources/math/i128.move:181:5+1
    assume {:print "$at(6,4693,4694)"} true;
L1:

    // return $t5 at ./sources/math/i128.move:181:5+1
    assume {:print "$at(6,4693,4694)"} true;
    $ret0 := $t5;
    return;

    // label L2 at ./sources/math/i128.move:181:5+1
L2:

    // abort($t4) at ./sources/math/i128.move:181:5+1
    assume {:print "$at(6,4693,4694)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun i128::neg_from [baseline] at ./sources/math/i128.move:32:5+305
procedure {:inline 1} $aa_i128_neg_from(_$t0: bv128) returns ($ret0: $aa_i128_I128)
{
    // declare local variables
    var $t1: $aa_i128_I128;
    var $t2: bv128;
    var $t3: bool;
    var $t4: bv128;
    var $t5: bool;
    var $t6: $aa_i128_I128;
    var $t7: bv128;
    var $t8: int;
    var $t9: bv128;
    var $t10: bv128;
    var $t11: int;
    var $t12: bv128;
    var $t13: $aa_i128_I128;
    var $t14: int;
    var $t15: int;
    var $t0: bv128;
    var $temp_0'$aa_i128_I128': $aa_i128_I128;
    var $temp_0'bv128': bv128;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at ./sources/math/i128.move:32:5+1
    assume {:print "$at(6,618,619)"} true;
    assume {:print "$track_local(100,17,0):", $t0} $t0 == $t0;

    // $t2 := 170141183460469231731687303715884105728 at ./sources/math/i128.move:33:22+11
    assume {:print "$at(6,676,687)"} true;
    $t2 := 170141183460469231731687303715884105728bv128;
    assume $IsValid'bv128'($t2);

    // $t3 := <=($t0, $t2) at ./sources/math/i128.move:33:17+16
    call $t3 := $LeBv128($t0, $t2);

    // if ($t3) goto L1 else goto L0 at ./sources/math/i128.move:33:9+6
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at ./sources/math/i128.move:34:13+1
    assume {:print "$at(6,737,738)"} true;
L1:

    // $t4 := 0 at ./sources/math/i128.move:34:18+1
    assume {:print "$at(6,742,743)"} true;
    $t4 := 0bv128;
    assume $IsValid'bv128'($t4);

    // $t5 := ==($t0, $t4) at ./sources/math/i128.move:34:13+6
    $t5 := $IsEqual'bv128'($t0, $t4);

    // if ($t5) goto L3 else goto L2 at ./sources/math/i128.move:34:9+184
    if ($t5) { goto L3; } else { goto L2; }

    // label L3 at ./sources/math/i128.move:35:13+44
    assume {:print "$at(6,759,803)"} true;
L3:

    // $t6 := pack 0xaa::i128::I128($t0) at ./sources/math/i128.move:35:13+44
    assume {:print "$at(6,759,803)"} true;
    $t6 := $aa_i128_I128($t0);

    // $t1 := $t6 at ./sources/math/i128.move:35:13+44
    $t1 := $t6;

    // trace_local[return]($t6) at ./sources/math/i128.move:35:13+44
    assume {:print "$track_local(100,17,1):", $t6} $t6 == $t6;

    // label L4 at ./sources/math/i128.move:32:40+270
    assume {:print "$at(6,653,923)"} true;
L4:

    // trace_return[0]($t1) at ./sources/math/i128.move:32:40+270
    assume {:print "$at(6,653,923)"} true;
    assume {:print "$track_return(100,17,0):", $t1} $t1 == $t1;

    // goto L5 at ./sources/math/i128.move:32:40+270
    goto L5;

    // label L2 at ./sources/math/i128.move:40:24+11
    assume {:print "$at(6,863,874)"} true;
L2:

    // $t7 := i128::u128_neg($t0) on_abort goto L6 with $t8 at ./sources/math/i128.move:40:24+11
    assume {:print "$at(6,863,874)"} true;
    call $t7 := $aa_i128_u128_neg($t0);
    if ($abort_flag) {
        assume {:print "$at(6,863,874)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(100,17):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t9 := 1 at ./sources/math/i128.move:40:39+1
    $t9 := 1bv128;
    assume $IsValid'bv128'($t9);

    // $t10 := +($t7, $t9) on_abort goto L6 with $t8 at ./sources/math/i128.move:40:23+18
    call $t10 := $AddBv128($t7, $t9);
    if ($abort_flag) {
        assume {:print "$at(6,862,880)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(100,17):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t11 := 170141183460469231731687303715884105728 at ./sources/math/i128.move:40:44+10
    $t11 := 170141183460469231731687303715884105728;
    assume $IsValid'u128'($t11);

    // $t12 := |($t10, $t11) at ./sources/math/i128.move:40:23+31
    call $t12 := $OrBv128($t10, $int2bv.128($t11));

    // $t13 := pack 0xaa::i128::I128($t12) at ./sources/math/i128.move:39:13+74
    assume {:print "$at(6,833,907)"} true;
    $t13 := $aa_i128_I128($t12);

    // $t1 := $t13 at ./sources/math/i128.move:39:13+74
    $t1 := $t13;

    // trace_local[return]($t13) at ./sources/math/i128.move:39:13+74
    assume {:print "$track_local(100,17,1):", $t13} $t13 == $t13;

    // goto L4 at ./sources/math/i128.move:39:13+74
    goto L4;

    // label L0 at ./sources/math/i128.move:33:59+8
    assume {:print "$at(6,713,721)"} true;
L0:

    // $t14 := 0 at ./sources/math/i128.move:33:59+8
    assume {:print "$at(6,713,721)"} true;
    $t14 := 0;
    assume $IsValid'u64'($t14);

    // $t15 := error::invalid_argument($t14) on_abort goto L6 with $t8 at ./sources/math/i128.move:33:35+33
    call $t15 := $1_error_invalid_argument($t14);
    if ($abort_flag) {
        assume {:print "$at(6,689,722)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(100,17):", $t8} $t8 == $t8;
        goto L6;
    }

    // trace_abort($t15) at ./sources/math/i128.move:33:9+6
    assume {:print "$at(6,663,669)"} true;
    assume {:print "$track_abort(100,17):", $t15} $t15 == $t15;

    // $t8 := move($t15) at ./sources/math/i128.move:33:9+6
    $t8 := $t15;

    // goto L6 at ./sources/math/i128.move:33:9+6
    goto L6;

    // label L5 at ./sources/math/i128.move:43:5+1
    assume {:print "$at(6,922,923)"} true;
L5:

    // return $t1 at ./sources/math/i128.move:43:5+1
    assume {:print "$at(6,922,923)"} true;
    $ret0 := $t1;
    return;

    // label L6 at ./sources/math/i128.move:43:5+1
L6:

    // abort($t8) at ./sources/math/i128.move:43:5+1
    assume {:print "$at(6,922,923)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun i128::u8_neg [baseline] at ./sources/math/i128.move:234:5+46
procedure {:inline 1} $aa_i128_u8_neg(_$t0: int) returns ($ret0: bv8)
{
    // declare local variables
    var $t1: int;
    var $t2: bv8;
    var $t0: int;
    var $temp_0'u8': int;
    var $temp_0'bv8': bv8;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at ./sources/math/i128.move:234:5+1
    assume {:print "$at(6,5850,5851)"} true;
    assume {:print "$track_local(100,21,0):", $t0} $t0 == $t0;

    // $t1 := 255 at ./sources/math/i128.move:235:13+4
    assume {:print "$at(6,5886,5890)"} true;
    $t1 := 255;
    assume $IsValid'u8'($t1);

    // $t2 := ^($t0, $t1) at ./sources/math/i128.move:235:9+8
    call $t2 := $XorBv8($int2bv.8($t0), $int2bv.8($t1));

    // trace_return[0]($t2) at ./sources/math/i128.move:235:9+8
    assume {:print "$track_return(100,21,0):", $t2} $t2 == $t2;

    // label L1 at ./sources/math/i128.move:236:5+1
    assume {:print "$at(6,5895,5896)"} true;
L1:

    // return $t2 at ./sources/math/i128.move:236:5+1
    assume {:print "$at(6,5895,5896)"} true;
    $ret0 := $t2;
    return;

}

// fun i128::wrapping_add [baseline] at ./sources/math/i128.move:53:5+349
procedure {:inline 1} $aa_i128_wrapping_add(_$t0: $aa_i128_I128, _$t1: $aa_i128_I128) returns ($ret0: $aa_i128_I128)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: bv128;
    var $t9: int;
    var $t10: int;
    var $t11: bv128;
    var $t12: bv8;
    var $t13: bv128;
    var $t14: int;
    var $t15: int;
    var $t16: bool;
    var $t17: int;
    var $t18: bv128;
    var $t19: bv128;
    var $t20: bv8;
    var $t21: bv128;
    var $t22: $aa_i128_I128;
    var $t0: $aa_i128_I128;
    var $t1: $aa_i128_I128;
    var $temp_0'$aa_i128_I128': $aa_i128_I128;
    var $temp_0'u128': int;
    var $temp_0'bv128': bv128;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[num1]($t0) at ./sources/math/i128.move:53:5+1
    assume {:print "$at(6,1072,1073)"} true;
    assume {:print "$track_local(100,22,0):", $t0} $t0 == $t0;

    // trace_local[num2]($t1) at ./sources/math/i128.move:53:5+1
    assume {:print "$track_local(100,22,1):", $t1} $t1 == $t1;

    // $t6 := get_field<0xaa::i128::I128>.bits($t0) at ./sources/math/i128.move:54:19+9
    assume {:print "$at(6,1145,1154)"} true;
    $t6 := $Bv128ToInt($t0->$bits);

    // $t7 := get_field<0xaa::i128::I128>.bits($t1) at ./sources/math/i128.move:54:31+9
    $t7 := $Bv128ToInt($t1->$bits);

    // $t8 := ^($t6, $t7) at ./sources/math/i128.move:54:19+21
    call $t8 := $XorBv128($int2bv.128($t6), $int2bv.128($t7));

    // trace_local[$t4]($t8) at ./sources/math/i128.move:54:19+21
    assume {:print "$track_local(100,22,2):", $t8} $t8 == $t8;

    // $t9 := get_field<0xaa::i128::I128>.bits($t0) at ./sources/math/i128.move:55:22+9
    assume {:print "$at(6,1189,1198)"} true;
    $t9 := $Bv128ToInt($t0->$bits);

    // $t10 := get_field<0xaa::i128::I128>.bits($t1) at ./sources/math/i128.move:55:34+9
    $t10 := $Bv128ToInt($t1->$bits);

    // $t11 := &($t9, $t10) at ./sources/math/i128.move:55:21+23
    call $t11 := $AndBv128($int2bv.128($t9), $int2bv.128($t10));

    // $t12 := 1 at ./sources/math/i128.move:55:48+1
    $t12 := 1bv8;
    assume $IsValid'bv8'($t12);

    // $t13 := <<($t11, $t12) on_abort goto L5 with $t14 at ./sources/math/i128.move:55:21+28
    call $t13 := $ShlBv128From8($t11, $t12);
    if ($abort_flag) {
        assume {:print "$at(6,1188,1216)"} true;
        $t14 := $abort_code;
        assume {:print "$track_abort(100,22):", $t14} $t14 == $t14;
        goto L5;
    }

    // trace_local[$t7]($t13) at ./sources/math/i128.move:55:21+28
    assume {:print "$track_local(100,22,3):", $t13} $t13 == $t13;

    // label L2 at ./sources/math/i128.move:56:16+5
    assume {:print "$at(6,1233,1238)"} true;
L2:

    // $t2 := havoc[val]() at ./sources/math/i128.move:56:16+5
    assume {:print "$at(6,1233,1238)"} true;
    havoc $t2;

    // assume WellFormed($t2) at ./sources/math/i128.move:56:16+5
    assume $IsValid'u128'($t2);

    // $t3 := havoc[val]() at ./sources/math/i128.move:56:16+5
    havoc $t3;

    // assume WellFormed($t3) at ./sources/math/i128.move:56:16+5
    assume $IsValid'u128'($t3);

    // $t15 := havoc[val]() at ./sources/math/i128.move:56:16+5
    havoc $t15;

    // assume WellFormed($t15) at ./sources/math/i128.move:56:16+5
    assume $IsValid'u128'($t15);

    // $t16 := havoc[val]() at ./sources/math/i128.move:56:16+5
    havoc $t16;

    // assume WellFormed($t16) at ./sources/math/i128.move:56:16+5
    assume $IsValid'bool'($t16);

    // $t17 := havoc[val]() at ./sources/math/i128.move:56:16+5
    havoc $t17;

    // assume WellFormed($t17) at ./sources/math/i128.move:56:16+5
    assume $IsValid'u128'($t17);

    // $t18 := havoc[val]() at ./sources/math/i128.move:56:16+5
    havoc $t18;

    // assume WellFormed($t18) at ./sources/math/i128.move:56:16+5
    assume $IsValid'bv128'($t18);

    // $t19 := havoc[val]() at ./sources/math/i128.move:56:16+5
    havoc $t19;

    // assume WellFormed($t19) at ./sources/math/i128.move:56:16+5
    assume $IsValid'bv128'($t19);

    // $t20 := havoc[val]() at ./sources/math/i128.move:56:16+5
    havoc $t20;

    // assume WellFormed($t20) at ./sources/math/i128.move:56:16+5
    assume $IsValid'bv8'($t20);

    // $t21 := havoc[val]() at ./sources/math/i128.move:56:16+5
    havoc $t21;

    // assume WellFormed($t21) at ./sources/math/i128.move:56:16+5
    assume $IsValid'bv128'($t21);

    // trace_local[$t4]($t2) at ./sources/math/i128.move:56:16+5
    assume {:print "$info(): enter loop, variable(s) $t4, $t7 havocked and reassigned"} true;
    assume {:print "$track_local(100,22,2):", $t2} $t2 == $t2;

    // trace_local[$t7]($t3) at ./sources/math/i128.move:56:16+5
    assume {:print "$track_local(100,22,3):", $t3} $t3 == $t3;

    // assume Not(AbortFlag()) at ./sources/math/i128.move:56:16+5
    assume !$abort_flag;

    // $t15 := 0 at ./sources/math/i128.move:56:25+1
    $t15 := 0;
    assume $IsValid'u128'($t15);

    // $t16 := !=($t3, $t15) at ./sources/math/i128.move:56:16+10
    $t16 := !$IsEqual'u128'($t3, $t15);

    // if ($t16) goto L1 else goto L0 at ./sources/math/i128.move:56:9+141
    if ($t16) { goto L1; } else { goto L0; }

    // label L1 at ./sources/math/i128.move:57:21+3
    assume {:print "$at(6,1267,1270)"} true;
L1:

    // $t17 := move($t2) at ./sources/math/i128.move:57:21+3
    assume {:print "$at(6,1267,1270)"} true;
    $t17 := $t2;

    // trace_local[$t15]($t2) at ./sources/math/i128.move:57:21+3
    assume {:print "$track_local(100,22,4):", $t2} $t2 == $t2;

    // trace_local[$t21]($t3) at ./sources/math/i128.move:58:21+5
    assume {:print "$at(6,1292,1297)"} true;
    assume {:print "$track_local(100,22,5):", $t3} $t3 == $t3;

    // $t18 := ^($t2, $t3) at ./sources/math/i128.move:59:19+5
    assume {:print "$at(6,1317,1322)"} true;
    call $t18 := $XorBv128($int2bv.128($t2), $int2bv.128($t3));

    // trace_local[$t4]($t18) at ./sources/math/i128.move:59:13+11
    assume {:print "$track_local(100,22,2):", $t18} $t18 == $t18;

    // $t19 := &($t17, $t3) at ./sources/math/i128.move:60:21+7
    assume {:print "$at(6,1344,1351)"} true;
    call $t19 := $AndBv128($int2bv.128($t17), $int2bv.128($t3));

    // $t20 := 1 at ./sources/math/i128.move:60:32+1
    $t20 := 1bv8;
    assume $IsValid'bv8'($t20);

    // $t21 := <<($t19, $t20) on_abort goto L5 with $t14 at ./sources/math/i128.move:60:21+12
    call $t21 := $ShlBv128From8($t19, $t20);
    if ($abort_flag) {
        assume {:print "$at(6,1344,1356)"} true;
        $t14 := $abort_code;
        assume {:print "$track_abort(100,22):", $t14} $t14 == $t14;
        goto L5;
    }

    // trace_local[$t7]($t21) at ./sources/math/i128.move:60:13+20
    assume {:print "$track_local(100,22,3):", $t21} $t21 == $t21;

    // goto L3 at ./sources/math/i128.move:56:9+141
    assume {:print "$at(6,1226,1367)"} true;
    goto L3;

    // label L0 at ./sources/math/i128.move:62:9+38
    assume {:print "$at(6,1377,1415)"} true;
L0:

    // $t22 := pack 0xaa::i128::I128($t2) at ./sources/math/i128.move:62:9+38
    assume {:print "$at(6,1377,1415)"} true;
    $t22 := $aa_i128_I128($IntToBv128($t2));

    // trace_return[0]($t22) at ./sources/math/i128.move:53:58+296
    assume {:print "$at(6,1125,1421)"} true;
    assume {:print "$track_return(100,22,0):", $t22} $t22 == $t22;

    // goto L4 at ./sources/math/i128.move:53:58+296
    goto L4;

    // label L3 at ./sources/math/i128.move:62:9+38
    // Loop invariant checking block for the loop started with header: L2
    assume {:print "$at(6,1377,1415)"} true;
L3:

    // stop() at ./sources/math/i128.move:62:9+38
    assume {:print "$at(6,1377,1415)"} true;
    assume false;
    return;

    // label L4 at ./sources/math/i128.move:65:5+1
    assume {:print "$at(6,1420,1421)"} true;
L4:

    // return $t22 at ./sources/math/i128.move:65:5+1
    assume {:print "$at(6,1420,1421)"} true;
    $ret0 := $t22;
    return;

    // label L5 at ./sources/math/i128.move:65:5+1
L5:

    // abort($t14) at ./sources/math/i128.move:65:5+1
    assume {:print "$at(6,1420,1421)"} true;
    $abort_code := $t14;
    $abort_flag := true;
    return;

}

// fun i128::u128_neg [baseline] at ./sources/math/i128.move:230:5+83
procedure {:inline 1} $aa_i128_u128_neg(_$t0: bv128) returns ($ret0: bv128)
{
    // declare local variables
    var $t1: int;
    var $t2: bv128;
    var $t0: bv128;
    var $temp_0'bv128': bv128;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at ./sources/math/i128.move:230:5+1
    assume {:print "$at(6,5761,5762)"} true;
    assume {:print "$track_local(100,30,0):", $t0} $t0 == $t0;

    // $t1 := 340282366920938463463374607431768211455 at ./sources/math/i128.move:231:13+34
    assume {:print "$at(6,5804,5838)"} true;
    $t1 := 340282366920938463463374607431768211455;
    assume $IsValid'u128'($t1);

    // $t2 := ^($t0, $t1) at ./sources/math/i128.move:231:9+38
    call $t2 := $XorBv128($t0, $int2bv.128($t1));

    // trace_return[0]($t2) at ./sources/math/i128.move:231:9+38
    assume {:print "$track_return(100,30,0):", $t2} $t2 == $t2;

    // label L1 at ./sources/math/i128.move:232:5+1
    assume {:print "$at(6,5843,5844)"} true;
L1:

    // return $t2 at ./sources/math/i128.move:232:5+1
    assume {:print "$at(6,5843,5844)"} true;
    $ret0 := $t2;
    return;

}

// fun liquidity_math::add_delta [baseline] at ./sources/math/liquidity_math.move:5:5+78
procedure {:inline 1} $aa_liquidity_math_add_delta(_$t0: int, _$t1: bv128) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: bv128;
    var $temp_0'u128': int;
    var $temp_0'bv128': bv128;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[net]($t0) at ./sources/math/liquidity_math.move:5:5+1
    assume {:print "$at(9,94,95)"} true;
    assume {:print "$track_local(106,0,0):", $t0} $t0 == $t0;

    // trace_local[delta]($t1) at ./sources/math/liquidity_math.move:5:5+1
    assume {:print "$track_local(106,0,1):", $t1} $t1 == $t1;

    // $t2 := +($t0, $t1) on_abort goto L2 with $t3 at ./sources/math/liquidity_math.move:6:9+11
    assume {:print "$at(9,155,166)"} true;
    call $t2 := $AddU128($t0, $Bv128ToInt($t1));
    if ($abort_flag) {
        assume {:print "$at(9,155,166)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(106,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./sources/math/liquidity_math.move:6:9+11
    assume {:print "$track_return(106,0,0):", $t2} $t2 == $t2;

    // label L1 at ./sources/math/liquidity_math.move:7:5+1
    assume {:print "$at(9,171,172)"} true;
L1:

    // return $t2 at ./sources/math/liquidity_math.move:7:5+1
    assume {:print "$at(9,171,172)"} true;
    $ret0 := $t2;
    return;

    // label L2 at ./sources/math/liquidity_math.move:7:5+1
L2:

    // abort($t3) at ./sources/math/liquidity_math.move:7:5+1
    assume {:print "$at(9,171,172)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun liquidity_math::sub_delta [baseline] at ./sources/math/liquidity_math.move:9:5+78
procedure {:inline 1} $aa_liquidity_math_sub_delta(_$t0: int, _$t1: bv128) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: bv128;
    var $temp_0'u128': int;
    var $temp_0'bv128': bv128;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[net]($t0) at ./sources/math/liquidity_math.move:9:5+1
    assume {:print "$at(9,178,179)"} true;
    assume {:print "$track_local(106,1,0):", $t0} $t0 == $t0;

    // trace_local[delta]($t1) at ./sources/math/liquidity_math.move:9:5+1
    assume {:print "$track_local(106,1,1):", $t1} $t1 == $t1;

    // $t2 := -($t0, $t1) on_abort goto L2 with $t3 at ./sources/math/liquidity_math.move:10:9+11
    assume {:print "$at(9,239,250)"} true;
    call $t2 := $Sub($t0, $Bv128ToInt($t1));
    if ($abort_flag) {
        assume {:print "$at(9,239,250)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(106,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./sources/math/liquidity_math.move:10:9+11
    assume {:print "$track_return(106,1,0):", $t2} $t2 == $t2;

    // label L1 at ./sources/math/liquidity_math.move:11:5+1
    assume {:print "$at(9,255,256)"} true;
L1:

    // return $t2 at ./sources/math/liquidity_math.move:11:5+1
    assume {:print "$at(9,255,256)"} true;
    $ret0 := $t2;
    return;

    // label L2 at ./sources/math/liquidity_math.move:11:5+1
L2:

    // abort($t3) at ./sources/math/liquidity_math.move:11:5+1
    assume {:print "$at(9,255,256)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct tick::TickInfo at ./sources/v3/tick.move:11:5+1513
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

// struct tick::TickUpdatedEvent at ./sources/v3/tick.move:36:5+426
datatype $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent($tick: $aa_i32_I32, $liquidity_gross_before: int, $liquidity_gross_after: int, $liquidity_net_before: $aa_i128_I128, $liquidity_net_after: $aa_i128_I128, $flipped: bool, $fee_growth_updated: bool, $fee_growth_outside_a_before: int, $fee_growth_outside_b_before: int, $emissions_per_liquidity_incentive_outside_before: Vec (int))
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_tick(s: $aa_tick_TickUpdatedEvent, x: $aa_i32_I32): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(x, s->$liquidity_gross_before, s->$liquidity_gross_after, s->$liquidity_net_before, s->$liquidity_net_after, s->$flipped, s->$fee_growth_updated, s->$fee_growth_outside_a_before, s->$fee_growth_outside_b_before, s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_liquidity_gross_before(s: $aa_tick_TickUpdatedEvent, x: int): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(s->$tick, x, s->$liquidity_gross_after, s->$liquidity_net_before, s->$liquidity_net_after, s->$flipped, s->$fee_growth_updated, s->$fee_growth_outside_a_before, s->$fee_growth_outside_b_before, s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_liquidity_gross_after(s: $aa_tick_TickUpdatedEvent, x: int): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(s->$tick, s->$liquidity_gross_before, x, s->$liquidity_net_before, s->$liquidity_net_after, s->$flipped, s->$fee_growth_updated, s->$fee_growth_outside_a_before, s->$fee_growth_outside_b_before, s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_liquidity_net_before(s: $aa_tick_TickUpdatedEvent, x: $aa_i128_I128): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(s->$tick, s->$liquidity_gross_before, s->$liquidity_gross_after, x, s->$liquidity_net_after, s->$flipped, s->$fee_growth_updated, s->$fee_growth_outside_a_before, s->$fee_growth_outside_b_before, s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_liquidity_net_after(s: $aa_tick_TickUpdatedEvent, x: $aa_i128_I128): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(s->$tick, s->$liquidity_gross_before, s->$liquidity_gross_after, s->$liquidity_net_before, x, s->$flipped, s->$fee_growth_updated, s->$fee_growth_outside_a_before, s->$fee_growth_outside_b_before, s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_flipped(s: $aa_tick_TickUpdatedEvent, x: bool): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(s->$tick, s->$liquidity_gross_before, s->$liquidity_gross_after, s->$liquidity_net_before, s->$liquidity_net_after, x, s->$fee_growth_updated, s->$fee_growth_outside_a_before, s->$fee_growth_outside_b_before, s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_fee_growth_updated(s: $aa_tick_TickUpdatedEvent, x: bool): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(s->$tick, s->$liquidity_gross_before, s->$liquidity_gross_after, s->$liquidity_net_before, s->$liquidity_net_after, s->$flipped, x, s->$fee_growth_outside_a_before, s->$fee_growth_outside_b_before, s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_fee_growth_outside_a_before(s: $aa_tick_TickUpdatedEvent, x: int): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(s->$tick, s->$liquidity_gross_before, s->$liquidity_gross_after, s->$liquidity_net_before, s->$liquidity_net_after, s->$flipped, s->$fee_growth_updated, x, s->$fee_growth_outside_b_before, s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_fee_growth_outside_b_before(s: $aa_tick_TickUpdatedEvent, x: int): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(s->$tick, s->$liquidity_gross_before, s->$liquidity_gross_after, s->$liquidity_net_before, s->$liquidity_net_after, s->$flipped, s->$fee_growth_updated, s->$fee_growth_outside_a_before, x, s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $Update'$aa_tick_TickUpdatedEvent'_emissions_per_liquidity_incentive_outside_before(s: $aa_tick_TickUpdatedEvent, x: Vec (int)): $aa_tick_TickUpdatedEvent {
    $aa_tick_TickUpdatedEvent(s->$tick, s->$liquidity_gross_before, s->$liquidity_gross_after, s->$liquidity_net_before, s->$liquidity_net_after, s->$flipped, s->$fee_growth_updated, s->$fee_growth_outside_a_before, s->$fee_growth_outside_b_before, x)
}
function $IsValid'$aa_tick_TickUpdatedEvent'(s: $aa_tick_TickUpdatedEvent): bool {
    $IsValid'$aa_i32_I32'(s->$tick)
      && $IsValid'u128'(s->$liquidity_gross_before)
      && $IsValid'u128'(s->$liquidity_gross_after)
      && $IsValid'$aa_i128_I128'(s->$liquidity_net_before)
      && $IsValid'$aa_i128_I128'(s->$liquidity_net_after)
      && $IsValid'bool'(s->$flipped)
      && $IsValid'bool'(s->$fee_growth_updated)
      && $IsValid'u128'(s->$fee_growth_outside_a_before)
      && $IsValid'u128'(s->$fee_growth_outside_b_before)
      && $IsValid'vec'u128''(s->$emissions_per_liquidity_incentive_outside_before)
}
function {:inline} $IsEqual'$aa_tick_TickUpdatedEvent'(s1: $aa_tick_TickUpdatedEvent, s2: $aa_tick_TickUpdatedEvent): bool {
    $IsEqual'$aa_i32_I32'(s1->$tick, s2->$tick)
    && $IsEqual'u128'(s1->$liquidity_gross_before, s2->$liquidity_gross_before)
    && $IsEqual'u128'(s1->$liquidity_gross_after, s2->$liquidity_gross_after)
    && $IsEqual'$aa_i128_I128'(s1->$liquidity_net_before, s2->$liquidity_net_before)
    && $IsEqual'$aa_i128_I128'(s1->$liquidity_net_after, s2->$liquidity_net_after)
    && $IsEqual'bool'(s1->$flipped, s2->$flipped)
    && $IsEqual'bool'(s1->$fee_growth_updated, s2->$fee_growth_updated)
    && $IsEqual'u128'(s1->$fee_growth_outside_a_before, s2->$fee_growth_outside_a_before)
    && $IsEqual'u128'(s1->$fee_growth_outside_b_before, s2->$fee_growth_outside_b_before)
    && $IsEqual'vec'u128''(s1->$emissions_per_liquidity_incentive_outside_before, s2->$emissions_per_liquidity_incentive_outside_before)}

// fun tick::update [verification] at ./sources/v3/tick.move:114:5+3099
procedure {:timeLimit 500} $aa_tick_update$verify(_$t0: $Mutation ($aa_tick_TickInfo), _$t1: $aa_i32_I32, _$t2: int, _$t3: int, _$t4: int, _$t5: int, _$t6: Vec (int), _$t7: bool, _$t8: bv128, _$t9: $aa_i32_I32, _$t10: bool) returns ($ret0: bool, $ret1: $Mutation ($aa_tick_TickInfo))
{
    // declare local variables
    var $t11: int;
    var $t12: $aa_i128_I128;
    var $t13: int;
    var $t14: int;
    var $t15: Vec (int);
    var $t16: $Mutation (int);
    var $t17: $Mutation (Vec (int));
    var $t18: bool;
    var $t19: bool;
    var $t20: int;
    var $t21: $aa_i128_I128;
    var $t22: int;
    var $t23: int;
    var $t24: Vec (int);
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t28: $Mutation (int);
    var $t29: int;
    var $t30: bool;
    var $t31: bool;
    var $t32: $Mutation (int);
    var $t33: $Mutation (int);
    var $t34: $Mutation (int);
    var $t35: $Mutation (int);
    var $t36: $Mutation (Vec (int));
    var $t37: bool;
    var $t38: bool;
    var $t39: $Mutation (bool);
    var $t40: $aa_i128_I128;
    var $t41: $aa_i128_I128;
    var $t42: $aa_i128_I128;
    var $t43: $Mutation ($aa_i128_I128);
    var $t44: int;
    var $t45: bool;
    var $t46: int;
    var $t47: int;
    var $t48: bool;
    var $t49: bool;
    var $t50: int;
    var $t51: $aa_i128_I128;
    var $t52: $aa_tick_TickUpdatedEvent;
    var $t53: bool;
    var $t54: int;
    var $t55: int;
    var $t56: bool;
    var $t57: bool;
    var $t58: bool;
    var $t59: $aa_i128_I128;
    var $t60: $aa_i128_I128;
    var $t61: $aa_i128_I128;
    var $t62: $Mutation ($aa_i128_I128);
    var $t63: $aa_i128_I128;
    var $t64: $aa_i128_I128;
    var $t65: $aa_i128_I128;
    var $t66: $Mutation ($aa_i128_I128);
    var $t67: $aa_i128_I128;
    var $t68: $aa_i128_I128;
    var $t69: $aa_i128_I128;
    var $t70: $Mutation ($aa_i128_I128);
    var $t71: bool;
    var $t72: bool;
    var $t73: int;
    var $t74: int;
    var $t75: $Mutation (int);
    var $t0: $Mutation ($aa_tick_TickInfo);
    var $t1: $aa_i32_I32;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: Vec (int);
    var $t7: bool;
    var $t8: bv128;
    var $t9: $aa_i32_I32;
    var $t10: bool;
    var $temp_0'$aa_i128_I128': $aa_i128_I128;
    var $temp_0'$aa_i32_I32': $aa_i32_I32;
    var $temp_0'$aa_tick_TickInfo': $aa_tick_TickInfo;
    var $temp_0'bool': bool;
    var $temp_0'u128': int;
    var $temp_0'bv128': bv128;
    var $temp_0'vec'u128'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;
    $t4 := _$t4;
    $t5 := _$t5;
    $t6 := _$t6;
    $t7 := _$t7;
    $t8 := _$t8;
    $t9 := _$t9;
    $t10 := _$t10;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/v3/tick.move:114:5+1
    assume {:print "$at(24,5508,5509)"} true;
    assume $IsValid'$aa_tick_TickInfo'($Dereference($t0));

    // assume WellFormed($t1) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'$aa_i32_I32'($t1);

    // assume WellFormed($t2) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'u128'($t2);

    // assume WellFormed($t3) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'u128'($t3);

    // assume WellFormed($t4) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'u128'($t4);

    // assume WellFormed($t5) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'u128'($t5);

    // assume WellFormed($t6) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'vec'u128''($t6);

    // assume WellFormed($t7) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'bool'($t7);

    // assume WellFormed($t8) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'bv128'($t8);

    // assume WellFormed($t9) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'$aa_i32_I32'($t9);

    // assume WellFormed($t10) at ./sources/v3/tick.move:114:5+1
    assume $IsValid'bool'($t10);

    // trace_local[info]($t0) at ./sources/v3/tick.move:114:5+1
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // trace_local[tick_to_update]($t1) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,1):", $t1} $t1 == $t1;

    // trace_local[fee_growth_global_a]($t2) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,2):", $t2} $t2 == $t2;

    // trace_local[fee_growth_global_b]($t3) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,3):", $t3} $t3 == $t3;

    // trace_local[seconds_per_liquidity_oracle]($t4) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,4):", $t4} $t4 == $t4;

    // trace_local[seconds_per_liquidity_incentive]($t5) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,5):", $t5} $t5 == $t5;

    // trace_local[emissions_per_liquidity]($t6) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,6):", $t6} $t6 == $t6;

    // trace_local[direction]($t7) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,7):", $t7} $t7 == $t7;

    // trace_local[liquidity_delta]($t8) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,8):", $t8} $t8 == $t8;

    // trace_local[tick_current]($t9) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,9):", $t9} $t9 == $t9;

    // trace_local[upper]($t10) at ./sources/v3/tick.move:114:5+1
    assume {:print "$track_local(107,0,10):", $t10} $t10 == $t10;

    // $t20 := get_field<0xaa::tick::TickInfo>.liquidity_gross($t0) at ./sources/v3/tick.move:127:38+20
    assume {:print "$at(24,5956,5976)"} true;
    $t20 := $Dereference($t0)->$liquidity_gross;

    // trace_local[liquidity_gross_before]($t20) at ./sources/v3/tick.move:127:38+20
    assume {:print "$track_local(107,0,11):", $t20} $t20 == $t20;

    // $t21 := get_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:128:36+18
    assume {:print "$at(24,6013,6031)"} true;
    $t21 := $Dereference($t0)->$liquidity_net;

    // trace_local[liquidity_net_before]($t21) at ./sources/v3/tick.move:128:36+18
    assume {:print "$track_local(107,0,12):", $t21} $t21 == $t21;

    // $t22 := get_field<0xaa::tick::TickInfo>.fee_growth_outside_a($t0) at ./sources/v3/tick.move:129:43+25
    assume {:print "$at(24,6075,6100)"} true;
    $t22 := $Dereference($t0)->$fee_growth_outside_a;

    // trace_local[fee_growth_outside_a_before]($t22) at ./sources/v3/tick.move:129:43+25
    assume {:print "$track_local(107,0,13):", $t22} $t22 == $t22;

    // $t23 := get_field<0xaa::tick::TickInfo>.fee_growth_outside_b($t0) at ./sources/v3/tick.move:130:43+25
    assume {:print "$at(24,6144,6169)"} true;
    $t23 := $Dereference($t0)->$fee_growth_outside_b;

    // trace_local[fee_growth_outside_b_before]($t23) at ./sources/v3/tick.move:130:43+25
    assume {:print "$track_local(107,0,14):", $t23} $t23 == $t23;

    // $t24 := get_field<0xaa::tick::TickInfo>.emissions_per_liquidity_incentive_outside($t0) at ./sources/v3/tick.move:131:64+46
    assume {:print "$at(24,6234,6280)"} true;
    $t24 := $Dereference($t0)->$emissions_per_liquidity_incentive_outside;

    // trace_local[emissions_per_liquidity_incentive_outside_before]($t24) at ./sources/v3/tick.move:131:64+46
    assume {:print "$track_local(107,0,15):", $t24} $t24 == $t24;

    // if ($t7) goto L1 else goto L0 at ./sources/v3/tick.move:132:9+245
    assume {:print "$at(24,6290,6535)"} true;
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at ./sources/v3/tick.move:133:62+20
    assume {:print "$at(24,6368,6388)"} true;
L1:

    // $t25 := get_field<0xaa::tick::TickInfo>.liquidity_gross($t0) at ./sources/v3/tick.move:133:62+20
    assume {:print "$at(24,6368,6388)"} true;
    $t25 := $Dereference($t0)->$liquidity_gross;

    // $t26 := liquidity_math::add_delta($t25, $t8) on_abort goto L23 with $t27 at ./sources/v3/tick.move:133:36+64
    call $t26 := $aa_liquidity_math_add_delta($t25, $t8);
    if ($abort_flag) {
        assume {:print "$at(24,6342,6406)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t28 := borrow_field<0xaa::tick::TickInfo>.liquidity_gross($t0) at ./sources/v3/tick.move:133:13+20
    $t28 := $ChildMutation($t0, 0, $Dereference($t0)->$liquidity_gross);

    // write_ref($t28, $t26) at ./sources/v3/tick.move:133:13+87
    $t28 := $UpdateMutation($t28, $t26);

    // write_back[Reference($t0).liquidity_gross (u128)]($t28) at ./sources/v3/tick.move:133:13+87
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_liquidity_gross($Dereference($t0), $Dereference($t28)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:133:13+87
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // label L21 at ./sources/v3/tick.move:138:38+22
    assume {:print "$at(24,6575,6597)"} true;
L21:

    // $t29 := 0 at ./sources/v3/tick.move:138:64+1
    assume {:print "$at(24,6601,6602)"} true;
    $t29 := 0;
    assume $IsValid'u128'($t29);

    // $t30 := ==($t20, $t29) at ./sources/v3/tick.move:138:38+27
    $t30 := $IsEqual'u128'($t20, $t29);

    // if ($t30) goto L3 else goto L2 at ./sources/v3/tick.move:138:34+620
    if ($t30) { goto L3; } else { goto L2; }

    // label L3 at ./sources/v3/tick.move:139:25+14
    assume {:print "$at(24,6630,6644)"} true;
L3:

    // $t31 := i32::lte($t1, $t9) on_abort goto L23 with $t27 at ./sources/v3/tick.move:139:16+38
    assume {:print "$at(24,6621,6659)"} true;
    call $t31 := $aa_i32_lte($t1, $t9);
    if ($abort_flag) {
        assume {:print "$at(24,6621,6659)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // if ($t31) goto L5 else goto L4 at ./sources/v3/tick.move:139:13+528
    if ($t31) { goto L5; } else { goto L4; }

    // label L5 at ./sources/v3/tick.move:140:17+25
    assume {:print "$at(24,6679,6704)"} true;
L5:

    // $t32 := borrow_field<0xaa::tick::TickInfo>.fee_growth_outside_a($t0) at ./sources/v3/tick.move:140:17+25
    assume {:print "$at(24,6679,6704)"} true;
    $t32 := $ChildMutation($t0, 2, $Dereference($t0)->$fee_growth_outside_a);

    // trace_local[$t25]($t32) at ./sources/v3/tick.move:140:17+47
    $temp_0'u128' := $Dereference($t32);
    assume {:print "$track_local(107,0,16):", $temp_0'u128'} $temp_0'u128' == $temp_0'u128';

    // write_ref($t32, $t2) at ./sources/v3/tick.move:140:17+47
    $t32 := $UpdateMutation($t32, $t2);

    // write_back[Reference($t0).fee_growth_outside_a (u128)]($t32) at ./sources/v3/tick.move:140:17+47
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_fee_growth_outside_a($Dereference($t0), $Dereference($t32)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:140:17+47
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // $t33 := borrow_field<0xaa::tick::TickInfo>.fee_growth_outside_b($t0) at ./sources/v3/tick.move:141:17+25
    assume {:print "$at(24,6744,6769)"} true;
    $t33 := $ChildMutation($t0, 3, $Dereference($t0)->$fee_growth_outside_b);

    // trace_local[$t25]($t33) at ./sources/v3/tick.move:141:17+47
    $temp_0'u128' := $Dereference($t33);
    assume {:print "$track_local(107,0,16):", $temp_0'u128'} $temp_0'u128' == $temp_0'u128';

    // write_ref($t33, $t3) at ./sources/v3/tick.move:141:17+47
    $t33 := $UpdateMutation($t33, $t3);

    // write_back[Reference($t0).fee_growth_outside_b (u128)]($t33) at ./sources/v3/tick.move:141:17+47
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_fee_growth_outside_b($Dereference($t0), $Dereference($t33)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:141:17+47
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // $t34 := borrow_field<0xaa::tick::TickInfo>.seconds_per_liquidity_oracle_outside($t0) at ./sources/v3/tick.move:142:17+41
    assume {:print "$at(24,6809,6850)"} true;
    $t34 := $ChildMutation($t0, 5, $Dereference($t0)->$seconds_per_liquidity_oracle_outside);

    // trace_local[$t25]($t34) at ./sources/v3/tick.move:142:17+72
    $temp_0'u128' := $Dereference($t34);
    assume {:print "$track_local(107,0,16):", $temp_0'u128'} $temp_0'u128' == $temp_0'u128';

    // write_ref($t34, $t4) at ./sources/v3/tick.move:142:17+72
    $t34 := $UpdateMutation($t34, $t4);

    // write_back[Reference($t0).seconds_per_liquidity_oracle_outside (u128)]($t34) at ./sources/v3/tick.move:142:17+72
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_seconds_per_liquidity_oracle_outside($Dereference($t0), $Dereference($t34)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:142:17+72
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // $t35 := borrow_field<0xaa::tick::TickInfo>.seconds_per_liquidity_incentive_outside($t0) at ./sources/v3/tick.move:143:17+44
    assume {:print "$at(24,6899,6943)"} true;
    $t35 := $ChildMutation($t0, 6, $Dereference($t0)->$seconds_per_liquidity_incentive_outside);

    // trace_local[$t25]($t35) at ./sources/v3/tick.move:143:17+78
    $temp_0'u128' := $Dereference($t35);
    assume {:print "$track_local(107,0,16):", $temp_0'u128'} $temp_0'u128' == $temp_0'u128';

    // write_ref($t35, $t5) at ./sources/v3/tick.move:143:17+78
    $t35 := $UpdateMutation($t35, $t5);

    // write_back[Reference($t0).seconds_per_liquidity_incentive_outside (u128)]($t35) at ./sources/v3/tick.move:143:17+78
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_seconds_per_liquidity_incentive_outside($Dereference($t0), $Dereference($t35)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:143:17+78
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // $t36 := borrow_field<0xaa::tick::TickInfo>.emissions_per_liquidity_incentive_outside($t0) at ./sources/v3/tick.move:144:17+46
    assume {:print "$at(24,6995,7041)"} true;
    $t36 := $ChildMutation($t0, 7, $Dereference($t0)->$emissions_per_liquidity_incentive_outside);

    // trace_local[$t40]($t36) at ./sources/v3/tick.move:144:17+72
    $temp_0'vec'u128'' := $Dereference($t36);
    assume {:print "$track_local(107,0,17):", $temp_0'vec'u128''} $temp_0'vec'u128'' == $temp_0'vec'u128'';

    // write_ref($t36, $t6) at ./sources/v3/tick.move:144:17+72
    $t36 := $UpdateMutation($t36, $t6);

    // write_back[Reference($t0).emissions_per_liquidity_incentive_outside (vector<u128>)]($t36) at ./sources/v3/tick.move:144:17+72
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_emissions_per_liquidity_incentive_outside($Dereference($t0), $Dereference($t36)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:144:17+72
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // $t37 := true at ./sources/v3/tick.move:145:17+4
    assume {:print "$at(24,7085,7089)"} true;
    $t37 := true;
    assume $IsValid'bool'($t37);

    // $t18 := $t37 at ./sources/v3/tick.move:145:17+4
    $t18 := $t37;

    // trace_local[$t31]($t37) at ./sources/v3/tick.move:145:17+4
    assume {:print "$track_local(107,0,18):", $t37} $t37 == $t37;

    // label L20 at ./sources/v3/tick.move:152:28+4
    assume {:print "$at(24,7220,7224)"} true;
L20:

    // $t38 := true at ./sources/v3/tick.move:152:28+4
    assume {:print "$at(24,7220,7224)"} true;
    $t38 := true;
    assume $IsValid'bool'($t38);

    // $t39 := borrow_field<0xaa::tick::TickInfo>.initialized($t0) at ./sources/v3/tick.move:152:9+16
    $t39 := $ChildMutation($t0, 9, $Dereference($t0)->$initialized);

    // write_ref($t39, $t38) at ./sources/v3/tick.move:152:9+23
    $t39 := $UpdateMutation($t39, $t38);

    // write_back[Reference($t0).initialized (bool)]($t39) at ./sources/v3/tick.move:152:9+23
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_initialized($Dereference($t0), $Dereference($t39)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:152:9+23
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // if ($t10) goto L7 else goto L6 at ./sources/v3/tick.move:155:9+562
    assume {:print "$at(24,7350,7912)"} true;
    if ($t10) { goto L7; } else { goto L6; }

    // label L7 at ./sources/v3/tick.move:156:13+248
    assume {:print "$at(24,7375,7623)"} true;
L7:

    // if ($t7) goto L9 else goto L8 at ./sources/v3/tick.move:156:13+248
    assume {:print "$at(24,7375,7623)"} true;
    if ($t7) { goto L9; } else { goto L8; }

    // label L9 at ./sources/v3/tick.move:157:48+18
    assume {:print "$at(24,7438,7456)"} true;
L9:

    // $t40 := get_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:157:48+18
    assume {:print "$at(24,7438,7456)"} true;
    $t40 := $Dereference($t0)->$liquidity_net;

    // $t41 := i128::from($t8) on_abort goto L23 with $t27 at ./sources/v3/tick.move:157:68+27
    call $t41 := $aa_i128_from($t8);
    if ($abort_flag) {
        assume {:print "$at(24,7458,7485)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t42 := i128::sub($t40, $t41) on_abort goto L23 with $t27 at ./sources/v3/tick.move:157:38+58
    call $t42 := $aa_i128_sub($t40, $t41);
    if ($abort_flag) {
        assume {:print "$at(24,7428,7486)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t43 := borrow_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:157:17+18
    $t43 := $ChildMutation($t0, 1, $Dereference($t0)->$liquidity_net);

    // write_ref($t43, $t42) at ./sources/v3/tick.move:157:17+79
    $t43 := $UpdateMutation($t43, $t42);

    // write_back[Reference($t0).liquidity_net (0xaa::i128::I128)]($t43) at ./sources/v3/tick.move:157:17+79
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_liquidity_net($Dereference($t0), $Dereference($t43)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:157:17+79
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // label L17 at ./sources/v3/tick.move:170:27+22
    assume {:print "$at(24,7941,7963)"} true;
L17:

    // $t44 := 0 at ./sources/v3/tick.move:170:53+1
    assume {:print "$at(24,7967,7968)"} true;
    $t44 := 0;
    assume $IsValid'u128'($t44);

    // $t45 := ==($t20, $t44) at ./sources/v3/tick.move:170:27+27
    $t45 := $IsEqual'u128'($t20, $t44);

    // if ($t45) goto L11 else goto L10 at ./sources/v3/tick.move:170:23+187
    if ($t45) { goto L11; } else { goto L10; }

    // label L11 at ./sources/v3/tick.move:171:17+20
    assume {:print "$at(24,7988,8008)"} true;
L11:

    // $t46 := get_field<0xaa::tick::TickInfo>.liquidity_gross($t0) at ./sources/v3/tick.move:171:17+20
    assume {:print "$at(24,7988,8008)"} true;
    $t46 := $Dereference($t0)->$liquidity_gross;

    // $t47 := 0 at ./sources/v3/tick.move:171:41+1
    $t47 := 0;
    assume $IsValid'u128'($t47);

    // $t48 := !=($t46, $t47) at ./sources/v3/tick.move:171:17+25
    $t48 := !$IsEqual'u128'($t46, $t47);

    // if ($t48) goto L13 else goto L12 at ./sources/v3/tick.move:171:13+50
    if ($t48) { goto L13; } else { goto L12; }

    // label L13 at ./sources/v3/tick.move:171:46+4
L13:

    // $t49 := true at ./sources/v3/tick.move:171:46+4
    assume {:print "$at(24,8017,8021)"} true;
    $t49 := true;
    assume $IsValid'bool'($t49);

    // $t19 := $t49 at ./sources/v3/tick.move:171:46+4
    $t19 := $t49;

    // trace_local[$t41]($t49) at ./sources/v3/tick.move:171:46+4
    assume {:print "$track_local(107,0,19):", $t49} $t49 == $t49;

    // label L14 at ./sources/v3/tick.move:176:19+14
    assume {:print "$at(24,8182,8196)"} true;
L14:

    // $t50 := get_field<0xaa::tick::TickInfo>.liquidity_gross($t0) at ./sources/v3/tick.move:178:36+20
    assume {:print "$at(24,8269,8289)"} true;
    $t50 := $Dereference($t0)->$liquidity_gross;

    // $t51 := get_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:180:34+18
    assume {:print "$at(24,8358,8376)"} true;
    $t51 := $Dereference($t0)->$liquidity_net;

    // $t52 := pack 0xaa::tick::TickUpdatedEvent($t1, $t20, $t50, $t21, $t51, $t19, $t18, $t22, $t23, $t24) at ./sources/v3/tick.move:175:21+437
    assume {:print "$at(24,8146,8583)"} true;
    $t52 := $aa_tick_TickUpdatedEvent($t1, $t20, $t50, $t21, $t51, $t19, $t18, $t22, $t23, $t24);

    // opaque begin: event::emit<0xaa::tick::TickUpdatedEvent>($t52) at ./sources/v3/tick.move:175:9+450

    // opaque end: event::emit<0xaa::tick::TickUpdatedEvent>($t52) at ./sources/v3/tick.move:175:9+450

    // trace_return[0]($t19) at ./sources/v3/tick.move:126:13+2690
    assume {:print "$at(24,5917,8607)"} true;
    assume {:print "$track_return(107,0,0):", $t19} $t19 == $t19;

    // trace_local[info]($t0) at ./sources/v3/tick.move:126:13+2690
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // goto L22 at ./sources/v3/tick.move:126:13+2690
    goto L22;

    // label L12 at ./sources/v3/tick.move:171:58+5
    assume {:print "$at(24,8029,8034)"} true;
L12:

    // $t53 := false at ./sources/v3/tick.move:171:58+5
    assume {:print "$at(24,8029,8034)"} true;
    $t53 := false;
    assume $IsValid'bool'($t53);

    // $t19 := $t53 at ./sources/v3/tick.move:171:58+5
    $t19 := $t53;

    // trace_local[$t41]($t53) at ./sources/v3/tick.move:171:58+5
    assume {:print "$track_local(107,0,19):", $t53} $t53 == $t53;

    // goto L14 at ./sources/v3/tick.move:171:58+5
    goto L14;

    // label L10 at ./sources/v3/tick.move:173:17+20
    assume {:print "$at(24,8068,8088)"} true;
L10:

    // $t54 := get_field<0xaa::tick::TickInfo>.liquidity_gross($t0) at ./sources/v3/tick.move:173:17+20
    assume {:print "$at(24,8068,8088)"} true;
    $t54 := $Dereference($t0)->$liquidity_gross;

    // $t55 := 0 at ./sources/v3/tick.move:173:41+1
    $t55 := 0;
    assume $IsValid'u128'($t55);

    // $t56 := !=($t54, $t55) at ./sources/v3/tick.move:173:17+25
    $t56 := !$IsEqual'u128'($t54, $t55);

    // if ($t56) goto L16 else goto L15 at ./sources/v3/tick.move:173:13+50
    if ($t56) { goto L16; } else { goto L15; }

    // label L16 at ./sources/v3/tick.move:173:46+5
L16:

    // $t57 := false at ./sources/v3/tick.move:173:46+5
    assume {:print "$at(24,8097,8102)"} true;
    $t57 := false;
    assume $IsValid'bool'($t57);

    // $t19 := $t57 at ./sources/v3/tick.move:173:46+5
    $t19 := $t57;

    // trace_local[$t41]($t57) at ./sources/v3/tick.move:173:46+5
    assume {:print "$track_local(107,0,19):", $t57} $t57 == $t57;

    // goto L14 at ./sources/v3/tick.move:173:46+5
    goto L14;

    // label L15 at ./sources/v3/tick.move:173:59+4
L15:

    // $t58 := true at ./sources/v3/tick.move:173:59+4
    assume {:print "$at(24,8110,8114)"} true;
    $t58 := true;
    assume $IsValid'bool'($t58);

    // $t19 := $t58 at ./sources/v3/tick.move:173:59+4
    $t19 := $t58;

    // trace_local[$t41]($t58) at ./sources/v3/tick.move:173:59+4
    assume {:print "$track_local(107,0,19):", $t58} $t58 == $t58;

    // goto L14 at ./sources/v3/tick.move:173:59+4
    goto L14;

    // label L8 at ./sources/v3/tick.move:159:48+18
    assume {:print "$at(24,7556,7574)"} true;
L8:

    // $t59 := get_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:159:48+18
    assume {:print "$at(24,7556,7574)"} true;
    $t59 := $Dereference($t0)->$liquidity_net;

    // $t60 := i128::neg_from($t8) on_abort goto L23 with $t27 at ./sources/v3/tick.move:159:68+31
    call $t60 := $aa_i128_neg_from($t8);
    if ($abort_flag) {
        assume {:print "$at(24,7576,7607)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t61 := i128::sub($t59, $t60) on_abort goto L23 with $t27 at ./sources/v3/tick.move:159:38+62
    call $t61 := $aa_i128_sub($t59, $t60);
    if ($abort_flag) {
        assume {:print "$at(24,7546,7608)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t62 := borrow_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:159:17+18
    $t62 := $ChildMutation($t0, 1, $Dereference($t0)->$liquidity_net);

    // write_ref($t62, $t61) at ./sources/v3/tick.move:159:17+83
    $t62 := $UpdateMutation($t62, $t61);

    // write_back[Reference($t0).liquidity_net (0xaa::i128::I128)]($t62) at ./sources/v3/tick.move:159:17+83
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_liquidity_net($Dereference($t0), $Dereference($t62)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:159:17+83
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // goto L17 at ./sources/v3/tick.move:159:17+83
    goto L17;

    // label L6 at ./sources/v3/tick.move:162:13+248
    assume {:print "$at(24,7653,7901)"} true;
L6:

    // if ($t7) goto L19 else goto L18 at ./sources/v3/tick.move:162:13+248
    assume {:print "$at(24,7653,7901)"} true;
    if ($t7) { goto L19; } else { goto L18; }

    // label L19 at ./sources/v3/tick.move:163:48+18
    assume {:print "$at(24,7716,7734)"} true;
L19:

    // $t63 := get_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:163:48+18
    assume {:print "$at(24,7716,7734)"} true;
    $t63 := $Dereference($t0)->$liquidity_net;

    // $t64 := i128::from($t8) on_abort goto L23 with $t27 at ./sources/v3/tick.move:163:68+27
    call $t64 := $aa_i128_from($t8);
    if ($abort_flag) {
        assume {:print "$at(24,7736,7763)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t65 := i128::add($t63, $t64) on_abort goto L23 with $t27 at ./sources/v3/tick.move:163:38+58
    call $t65 := $aa_i128_add($t63, $t64);
    if ($abort_flag) {
        assume {:print "$at(24,7706,7764)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t66 := borrow_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:163:17+18
    $t66 := $ChildMutation($t0, 1, $Dereference($t0)->$liquidity_net);

    // write_ref($t66, $t65) at ./sources/v3/tick.move:163:17+79
    $t66 := $UpdateMutation($t66, $t65);

    // write_back[Reference($t0).liquidity_net (0xaa::i128::I128)]($t66) at ./sources/v3/tick.move:163:17+79
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_liquidity_net($Dereference($t0), $Dereference($t66)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:163:17+79
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // goto L17 at ./sources/v3/tick.move:162:27+112
    assume {:print "$at(24,7667,7779)"} true;
    goto L17;

    // label L18 at ./sources/v3/tick.move:165:48+18
    assume {:print "$at(24,7834,7852)"} true;
L18:

    // $t67 := get_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:165:48+18
    assume {:print "$at(24,7834,7852)"} true;
    $t67 := $Dereference($t0)->$liquidity_net;

    // $t68 := i128::neg_from($t8) on_abort goto L23 with $t27 at ./sources/v3/tick.move:165:68+31
    call $t68 := $aa_i128_neg_from($t8);
    if ($abort_flag) {
        assume {:print "$at(24,7854,7885)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t69 := i128::add($t67, $t68) on_abort goto L23 with $t27 at ./sources/v3/tick.move:165:38+62
    call $t69 := $aa_i128_add($t67, $t68);
    if ($abort_flag) {
        assume {:print "$at(24,7824,7886)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t70 := borrow_field<0xaa::tick::TickInfo>.liquidity_net($t0) at ./sources/v3/tick.move:165:17+18
    $t70 := $ChildMutation($t0, 1, $Dereference($t0)->$liquidity_net);

    // write_ref($t70, $t69) at ./sources/v3/tick.move:165:17+83
    $t70 := $UpdateMutation($t70, $t69);

    // write_back[Reference($t0).liquidity_net (0xaa::i128::I128)]($t70) at ./sources/v3/tick.move:165:17+83
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_liquidity_net($Dereference($t0), $Dereference($t70)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:165:17+83
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // goto L17 at ./sources/v3/tick.move:165:17+83
    goto L17;

    // label L4 at ./sources/v3/tick.move:147:17+5
    assume {:print "$at(24,7127,7132)"} true;
L4:

    // $t71 := false at ./sources/v3/tick.move:147:17+5
    assume {:print "$at(24,7127,7132)"} true;
    $t71 := false;
    assume $IsValid'bool'($t71);

    // $t18 := $t71 at ./sources/v3/tick.move:147:17+5
    $t18 := $t71;

    // trace_local[$t31]($t71) at ./sources/v3/tick.move:147:17+5
    assume {:print "$track_local(107,0,18):", $t71} $t71 == $t71;

    // goto L20 at ./sources/v3/tick.move:147:17+5
    goto L20;

    // label L2 at ./sources/v3/tick.move:150:13+5
    assume {:print "$at(24,7176,7181)"} true;
L2:

    // $t72 := false at ./sources/v3/tick.move:150:13+5
    assume {:print "$at(24,7176,7181)"} true;
    $t72 := false;
    assume $IsValid'bool'($t72);

    // $t18 := $t72 at ./sources/v3/tick.move:150:13+5
    $t18 := $t72;

    // trace_local[$t31]($t72) at ./sources/v3/tick.move:150:13+5
    assume {:print "$track_local(107,0,18):", $t72} $t72 == $t72;

    // goto L20 at ./sources/v3/tick.move:150:13+5
    goto L20;

    // label L0 at ./sources/v3/tick.move:135:62+20
    assume {:print "$at(24,6486,6506)"} true;
L0:

    // $t73 := get_field<0xaa::tick::TickInfo>.liquidity_gross($t0) at ./sources/v3/tick.move:135:62+20
    assume {:print "$at(24,6486,6506)"} true;
    $t73 := $Dereference($t0)->$liquidity_gross;

    // $t74 := liquidity_math::sub_delta($t73, $t8) on_abort goto L23 with $t27 at ./sources/v3/tick.move:135:36+64
    call $t74 := $aa_liquidity_math_sub_delta($t73, $t8);
    if ($abort_flag) {
        assume {:print "$at(24,6460,6524)"} true;
        $t27 := $abort_code;
        assume {:print "$track_abort(107,0):", $t27} $t27 == $t27;
        goto L23;
    }

    // $t75 := borrow_field<0xaa::tick::TickInfo>.liquidity_gross($t0) at ./sources/v3/tick.move:135:13+20
    $t75 := $ChildMutation($t0, 0, $Dereference($t0)->$liquidity_gross);

    // write_ref($t75, $t74) at ./sources/v3/tick.move:135:13+87
    $t75 := $UpdateMutation($t75, $t74);

    // write_back[Reference($t0).liquidity_gross (u128)]($t75) at ./sources/v3/tick.move:135:13+87
    $t0 := $UpdateMutation($t0, $Update'$aa_tick_TickInfo'_liquidity_gross($Dereference($t0), $Dereference($t75)));

    // trace_local[info]($t0) at ./sources/v3/tick.move:135:13+87
    $temp_0'$aa_tick_TickInfo' := $Dereference($t0);
    assume {:print "$track_local(107,0,0):", $temp_0'$aa_tick_TickInfo'} $temp_0'$aa_tick_TickInfo' == $temp_0'$aa_tick_TickInfo';

    // goto L21 at ./sources/v3/tick.move:135:13+87
    goto L21;

    // label L22 at ./sources/v3/tick.move:188:5+1
    assume {:print "$at(24,8606,8607)"} true;
L22:

    // assert Implies(Eq<u128>(select tick::TickInfo.liquidity_gross<0xaa::tick::TickInfo>($t0), 0), Not(select tick::TickInfo.initialized<0xaa::tick::TickInfo>($t0))) at ./sources/v3/tick.move:109:9+56
    assume {:print "$at(24,5299,5355)"} true;
    assert {:msg "assert_failed(24,5299,5355): post-condition does not hold"}
      ($IsEqual'u128'($Dereference($t0)->$liquidity_gross, 0) ==> !$Dereference($t0)->$initialized);

    // assert Implies(Gt(select tick::TickInfo.liquidity_gross<0xaa::tick::TickInfo>($t0), 0), select tick::TickInfo.initialized<0xaa::tick::TickInfo>($t0)) at ./sources/v3/tick.move:110:9+54
    assume {:print "$at(24,5364,5418)"} true;
    assert {:msg "assert_failed(24,5364,5418): post-condition does not hold"}
      (($Dereference($t0)->$liquidity_gross > 0) ==> $Dereference($t0)->$initialized);

    // return $t19 at ./sources/v3/tick.move:110:9+54
    $ret0 := $t19;
    $ret1 := $t0;
    return;

    // label L23 at ./sources/v3/tick.move:188:5+1
    assume {:print "$at(24,8606,8607)"} true;
L23:

    // abort($t27) at ./sources/v3/tick.move:188:5+1
    assume {:print "$at(24,8606,8607)"} true;
    $abort_code := $t27;
    $abort_flag := true;
    return;

}
