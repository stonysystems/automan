include "../../Protocol/SHT/Delegations.i.dfy"
include "../../Common/Collections/Maps2.s.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../Common/GenericRefinement.i.dfy"

module SHT__CDelegations_i {
import opened Native__NativeTypes_s
import opened Collections__Maps2_s
import opened Native__Io_s
import opened SHT__Delegations_i
import opened Common__NodeIdentity_i
import opened AppInterface_i`Spec
import opened SHT__Keys_i
import opened GenericRefinement_i
import opened SHT__HT_s
import opened Concrete_NodeIdentity_i

datatype Mapping = Mapping(klo:KeyPlus, id:EndPoint)
datatype CDelegationMap = CDelegationMap(lows:seq<Mapping>)

predicate CDelegationMapHasValidEndPoints(lows:seq<Mapping>)
{
    forall m :: m in lows ==> EndPointIsAbstractable(m.id)
}

predicate CDelegationMapBoundedSize(m:CDelegationMap)
{
    0 < |m.lows| < 0x1_0000_0000_0000_0000 - 1
}

predicate CDelegationMapIsSorted_Helper(m:CDelegationMap)
    requires CDelegationMapBoundedSize(m)
{
    forall i {:trigger KeyPlusLt(m.lows[i].klo, m.lows[i+1].klo)} :: 0<=i<|m.lows|-1
        ==> KeyPlusLt(m.lows[i].klo, m.lows[i+1].klo)
}

predicate CDelegationMapIsSorted(m:CDelegationMap)
{
       CDelegationMapBoundedSize(m)
    && CDelegationMapIsSorted_Helper(m)
    && KeyPlusLt(m.lows[|m.lows|-1].klo, KeyInf())
}

predicate CDelegationMapIsComplete(m:CDelegationMap)
{
    CDelegationMapBoundedSize(m) && CDelegationMapIsSorted(m) && m.lows[0].klo == KeyZero()
}

predicate CDelegationMapIsValid(m:CDelegationMap)
{
       CDelegationMapHasValidEndPoints(m.lows)
    && CDelegationMapIsComplete(m)
}


predicate CDelegationMapIsAbstractable(m:CDelegationMap)
{
    CDelegationMapIsValid(m)
}

lemma CDelegationMapIsSortedExtension_recursive(m:CDelegationMap, i:int, j:int)
    requires 0<=i<j<|m.lows|;
    requires CDelegationMapIsSorted(m);
    ensures  KeyPlusLt(m.lows[i].klo, m.lows[j].klo);
{
    if (j==i+1) {
    } else {
        CDelegationMapIsSortedExtension_recursive(m, i, j-1);
        KeyPlusTransitivity(m.lows[i].klo, m.lows[j-1].klo, m.lows[j].klo);
        var ji := j-1; 
        assert KeyPlusLt(m.lows[ji].klo, m.lows[ji+1].klo); // OBSERVE trigger
    }
}

lemma CDelegationMapIsSortedExtension(m:CDelegationMap)
    requires CDelegationMapIsSorted(m);
    ensures forall i,j :: 0<=i<j<|m.lows| ==> KeyPlusLt(m.lows[i].klo, m.lows[j].klo);
{
    forall i,j | 0<=i<j<|m.lows| ensures KeyPlusLt(m.lows[i].klo, m.lows[j].klo);
    {
        CDelegationMapIsSortedExtension_recursive(m, i, j);
    }
}

function CDM_IndexToNextKeyBoundary(m:CDelegationMap, i:int) : KeyPlus
    requires 0 <= i < |m.lows|;
{
    if i < |m.lows| - 1 then m.lows[i+1].klo else KeyInf()
}

function CDM_IndexRangeToKeyRange(m:CDelegationMap, i:int, j:int) : KeyRange
    requires 0<=i<=j<|m.lows|;
{
    KeyRange(m.lows[i].klo, CDM_IndexToNextKeyBoundary(m, j))
}

function CDM_IndexToKeyRange(m:CDelegationMap, idx:int) : KeyRange
    requires 0<=idx<|m.lows|;
{
    CDM_IndexRangeToKeyRange(m, idx, idx)
}

function method {:opaque} CDM_IndexForKey_helper(m:CDelegationMap, k:KeyPlus, index:uint64) : uint64
    requires CDelegationMapIsValid(m);
    requires forall i :: 0 <= i <= index as int && i < |m.lows| ==> KeyPlusLe(m.lows[i].klo, k);
    decreases |m.lows| - index as int;
    ensures  0 <= CDM_IndexForKey_helper(m, k, index) as int < |m.lows|;
    ensures  !k.KeyInf? ==> KeyRangeContains(CDM_IndexToKeyRange(m, CDM_IndexForKey_helper(m, k, index) as int), k);
    ensures k.KeyInf? ==> CDM_IndexForKey_helper(m, k, index) as int == |m.lows| - 1;
{
    CDelegationMapIsSortedExtension(m);
    if index >= (|m.lows| as uint64 - 1) as uint64 then
        (|m.lows| as uint64 - 1) as uint64
    else if KeyPlusLt(k, m.lows[index + 1].klo) then
        index
    else
        KeyPlusAntisymmetry(k, m.lows[index+1].klo);
        CDM_IndexForKey_helper(m, k, index + 1)
}

function method CDM_IndexForKey(m:CDelegationMap, k:KeyPlus) : uint64
    requires 0<|m.lows|;
    requires CDelegationMapIsValid(m);
    ensures 0 <= CDM_IndexForKey(m, k) as int < |m.lows|;
    ensures !k.KeyInf? ==> KeyRangeContains(CDM_IndexToKeyRange(m, CDM_IndexForKey(m, k) as int), k);
    ensures k.KeyInf? ==> CDM_IndexForKey(m, k) as int == |m.lows| - 1;
{
    //IndexForKeyAccurate(m, k, 0); 
    CDM_IndexForKey_helper(m, k, 0)
}

function RefineToDelegationMapEntry(m:CDelegationMap, k:Key) : NodeIdentity
    requires CDelegationMapIsAbstractable(m);
    requires forall low :: low in m.lows ==> EndPointIsValid(low.id);
{
    AbstractifyEndPointToNodeIdentity(m.lows[CDM_IndexForKey(m,KeyPlus(k))].id)
}

function AbstractifyCDelegationMapToDelegationMap(m:CDelegationMap) : DelegationMap
    requires CDelegationMapIsAbstractable(m);
    requires forall low :: low in m.lows ==> EndPointIsValid(low.id);
{
    map k:Key {:trigger CDM_IndexForKey(m,KeyPlus(k))} :: RefineToDelegationMapEntry(m, k)
}

function method DelegateForKeyImpl(m:CDelegationMap, k:Key) : (EndPoint)
    requires 0<|m.lows|;
     requires CDelegationMapIsValid(m);
     ensures var ep := DelegateForKeyImpl(m,k);
                EndPointIsValid(ep)
                && AbstractifyCDelegationMapToDelegationMap(m)[k] == AbstractifyEndPointToNodeIdentity(ep)
                && AbstractifyEndPointToNodeIdentity(ep) == DelegateForKey(AbstractifyCDelegationMapToDelegationMap(m), k);
{
    // print "key: ", k, "\n";
    var idx := CDM_IndexForKey(m,KeyPlus(k));
    // print "belongs to node ", idx, " \n";
    m.lows[CDM_IndexForKey(m,KeyPlus(k))].id
}


lemma CDM_IndexForKey_Ordering(m:CDelegationMap)
    requires CDelegationMapIsValid(m);
    ensures  forall k1, k2 :: KeyPlusLe(k1, k2) ==> CDM_IndexForKey(m, k1) <= CDM_IndexForKey(m, k2);
{
    forall k1, k2 | KeyPlusLe(k1, k2) 
        ensures CDM_IndexForKey(m, k1) <= CDM_IndexForKey(m, k2);
    {
        var index1 :=  CDM_IndexForKey(m, k1) as int;
        var index2 :=  CDM_IndexForKey(m, k2) as int;
        CDelegationMapIsSortedExtension(m);
        KeyPlusAntisymmetry(k1, k2);

        if k1.KeyInf? {
            assert k2.KeyInf?;
            assert index1 == |m.lows|-1 == index2;
        } else if k2.KeyInf? {
            assert index2 == |m.lows|-1;
            assert index1 <= |m.lows|-1;
        } else {
            if index2 < index1 { // Suppose...
                var kr1 := CDM_IndexToKeyRange(m, index1);
                var kr2 := CDM_IndexToKeyRange(m, index2);

                assert KeyPlusLt(kr2.klo, kr1.klo);

                assert KeyPlusLe(kr1.klo, k1);
                assert KeyPlusLt(k1, kr1.khi);
                
                assert KeyPlusLe(kr2.klo, k2);
                assert KeyPlusLt(k2, kr2.khi);

                assert KeyPlusLe(kr2.khi, kr1.klo);

                KeyPlusTransitivity(k2, kr2.khi, kr1.klo);
                assert KeyPlusLe(k2, kr1.klo);
                KeyPlusTransitivity(k2, kr1.klo, k1);
                assert KeyPlusLe(k2, k1);

                assert false;
            }
            assert index1 <= index2;
        }
    }
}

lemma SequenceIndexingHelper<T>(a:seq<T>, b:seq<T>, c:seq<T>, d:seq<T>, combined:seq<T>, index:int)
    requires combined == a + b + c + d;
    requires index >= |a + b + c|;
    requires 0 <= index < |combined|
    ensures  combined[index] == d[index - |a + b + c|];
{
}


lemma CDM_KeyRangesAreOrdered(m:CDelegationMap, i1:int, i2:int)
    requires CDelegationMapIsSorted(m);
    requires 0<=i1<i2<|m.lows|;
    ensures KeyPlusLe(CDM_IndexToKeyRange(m, i1).khi, 
                     CDM_IndexToKeyRange(m, i2).klo);
    decreases i2-i1;
{
    //KeyPlusEq(CDM_IndexToKeyRange(m, i2-1).khi.k, CDM_IndexToKeyRange(m, i2).klo);
    if (i1+1<i2) {
        CDM_KeyRangesAreOrdered(m, i1, i2-1);   // recurse
        KeyPlusTransitivity(CDM_IndexToKeyRange(m, i1).khi, m.lows[i2-1].klo, 
                        CDM_IndexToKeyRange(m, i2).klo);
    }
}

lemma CDM_Partitioned(m:CDelegationMap, k:KeyPlus, index:int) 
    requires CDelegationMapIsValid(m);
    requires 0 <= index < |m.lows|;
    requires KeyRangeContains(CDM_IndexToKeyRange(m, index), k);
    ensures  forall i :: 0 <= i < |m.lows| && i != index ==> !KeyRangeContains(CDM_IndexToKeyRange(m, i), k);
{
    CDelegationMapIsSortedExtension(m);
    var real_kr := CDM_IndexToKeyRange(m, index);

    forall i | 0 <= i < |m.lows| && i != index
        ensures !KeyRangeContains(CDM_IndexToKeyRange(m, i), k);
    {
        if KeyRangeContains(CDM_IndexToKeyRange(m, i), k) { // Proof by contradiction
            var kr := CDM_IndexToKeyRange(m, i);
            if i < index {
                assert KeyPlusLt(k, kr.khi);
                CDM_KeyRangesAreOrdered(m, i, index);
                assert KeyPlusLe(kr.khi, real_kr.klo); 
                KeyPlusTransitivity(k, kr.khi, real_kr.klo);
                KeyPlusAntisymmetry(k, real_kr.klo);
                assert false;
            } else {
                assert KeyPlusLe(kr.klo, k);
                assert KeyPlusLt(k, real_kr.khi);
                CDM_KeyRangesAreOrdered(m, index, i);
                assert KeyPlusLe(real_kr.khi, kr.klo);
                KeyPlusTransitivity(real_kr.khi, kr.klo, k);
                KeyPlusAntisymmetry(real_kr.khi, k);
                assert false;
            }
        }
    }

}

lemma UpdateCDelegationMap_Part1(m:CDelegationMap, newkr:KeyRange, id:EndPoint, m':CDelegationMap,
                                 left_index:int, right_index:int, new_left:seq<Mapping>, new_right:seq<Mapping>)
    requires CDelegationMapIsValid(m);
    requires EndPointIsValid(id);
    requires !EmptyKeyRange(newkr);
    requires left_index == CDM_IndexForKey(m, newkr.klo) as int;
    requires right_index == CDM_IndexForKey(m, newkr.khi) as int;
    requires m.lows[left_index].klo != newkr.klo;
    requires new_left == m.lows[..left_index+1];
    requires new_right == if newkr.khi.KeyInf? then [] else [Mapping(newkr.khi, m.lows[right_index].id)] + m.lows[right_index+1..];
    requires m' == CDelegationMap(new_left + [Mapping(newkr.klo, id)] + new_right);
    requires CDelegationMapIsValid(m');
    ensures  AbstractifyCDelegationMapToDelegationMap(m') == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id));
    //ensures |m'.lows| as uint64 <= |m.lows| as uint64 + 1
{
    var rm  := AbstractifyCDelegationMapToDelegationMap(m);
    var rm' := AbstractifyCDelegationMapToDelegationMap(m');
    var updated_rm := UpdateDelegationMap(rm, newkr, AbstractifyEndPointToNodeIdentity(id));

    forall k:Key 
        ensures k in rm' <==> k in updated_rm;
    { 
    }

    forall k:Key 
        ensures rm'[k] == updated_rm[k];
    { 
        CDelegationMapIsSortedExtension(m);
        CDelegationMapIsSortedExtension(m');

        if KeyRangeContains(newkr, KeyPlus(k)) {
            //var k_index := CDM_IndexForKey(m', KeyPlus(k)) as int;
            var index := left_index + 1;
            assert m'.lows[index] == Mapping(newkr.klo, id);
            assert KeyRangeContains(CDM_IndexToKeyRange(m', index), KeyPlus(k));
            CDM_Partitioned(m', KeyPlus(k), index);
            assert CDM_IndexForKey(m', KeyPlus(k)) as int == index;
            assert rm'[k] == AbstractifyEndPointToNodeIdentity(id);
        } else {
            KeyPlusAntisymmetry(KeyPlus(k), newkr.khi);
            assert !KeyPlusLt(KeyPlus(k), newkr.khi) ==> KeyPlusLe(newkr.khi, KeyPlus(k));
            KeyPlusAntisymmetry(newkr.klo, KeyPlus(k));
            assert !KeyPlusLe(newkr.klo, KeyPlus(k)) ==> KeyPlusLt(KeyPlus(k), newkr.klo);
            assert KeyPlusLt(KeyPlus(k), newkr.klo) || KeyPlusLe(newkr.khi, KeyPlus(k));  // From !KeyRangeContains(newkr, k)

            var k_index := CDM_IndexForKey(m', KeyPlus(k)) as int;
            var new_index := left_index+1;  // Index of the new mapping, Mapping(newkr.klo, id)

            assert k_index != new_index;

            if k_index < new_index {
                var kr := CDM_IndexToKeyRange(m', k_index);

                if k_index == left_index {
                    assert KeyPlusLe(m.lows[left_index].klo, KeyPlus(k));
                    KeyPlusTransitivity(m.lows[left_index].klo, KeyPlus(k), newkr.klo);
                    assert KeyRangeContains(CDM_IndexToKeyRange(m', left_index), KeyPlus(k));
                    CDM_Partitioned(m', KeyPlus(k), left_index);
                    assert m'.lows[CDM_IndexForKey(m',KeyPlus(k))].id == m'.lows[k_index].id;
                    assert !newkr.klo.KeyInf?;
                    assert KeyRangeContains(CDM_IndexToKeyRange(m, left_index), newkr.klo);
                    //assert KeyPlusLt(newkr.klo, CDM_IndexToKeyRange(m, left_index).khi);
                    assert KeyPlusLt(newkr.klo, CDM_IndexToNextKeyBoundary(m, k_index));
                    KeyPlusTransitivity(KeyPlus(k), newkr.klo, CDM_IndexToNextKeyBoundary(m, k_index));
                    CDM_Partitioned(m, KeyPlus(k), k_index);
                    
                    assert rm'[k] == rm[k];
                } else {
                    assert k_index < left_index;
                    //assert CDM_IndexToKeyRange(m, k_index) == CDM_IndexToKeyRange(m', k_index);
                    CDM_Partitioned(m, KeyPlus(k), k_index);
                    assert m.lows[k_index] == m'.lows[k_index];
                    assert m.lows[CDM_IndexForKey(m,KeyPlus(k))] == m'.lows[CDM_IndexForKey(m',KeyPlus(k))];
                    assert rm'[k] == rm[k];
                }
//                assert KeyRangeContains(kr.klo, KeyPlus(k));
//                CDM_Partitioned(m', KeyPlus(k), k_index);
//                assert CDM_IndexForKey(m', KeyPlus(k)) as int == k_index;
                /*
                assert KeyPlusLt(KeyPlus(k), newkr.klo);
                if |m.lows| > 1 {
                    assert KeyPlusLt(newkr.klo, m.lows[1].klo);
                    KeyPlusTransitivity(KeyPlus(k), newkr.klo, m.lows[1].klo);
                    assert KeyRangeContains(CDM_IndexToKeyRange(m, 0), KeyPlus(k));
                    CDM_Partitioned(m, KeyPlus(k), 0);
                    assert CDM_IndexForKey(m, KeyPlus(k)) as int == 0;
                }
                calc {
                    rm'[k];
                    m.lows[0].id;
                    rm[k];
                }
                */
            } else {
                assert k_index > new_index;

                UpdateCDelegationMap_RHS(m, newkr, id, m', left_index, right_index, new_left, new_right, k, left_index+1);
            }

            assert rm'[k] == rm[k];

            calc {
                rm'[k];
                rm[k];
                updated_rm[k];
            }
        }
    }
    lemma_UpdateCDelegationMap_Part2_Helper(m, m', newkr, id);
}


lemma lemma_UpdateCDelegationMap_Part2_Helper(m:CDelegationMap, m':CDelegationMap, newkr:KeyRange, id:EndPoint)
    requires CDelegationMapIsValid(m);
    requires CDelegationMapIsValid(m');
    requires EndPointIsValid(id);
    requires !EmptyKeyRange(newkr);
    requires forall k:Key :: k in AbstractifyCDelegationMapToDelegationMap(m') <==> k in UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id));
    requires forall k:Key :: true ==> AbstractifyCDelegationMapToDelegationMap(m')[k] == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id))[k];
    ensures  AbstractifyCDelegationMapToDelegationMap(m') == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id));
{
}


lemma {:timeLimitMultiplier 16} UpdateCDelegationMap_RHS_Helper(m:CDelegationMap, newkr:KeyRange, id:EndPoint, m':CDelegationMap,
                               left_index:int, right_index:int, new_left:seq<Mapping>, new_right:seq<Mapping>,
                               k:Key, new_index:int)
    requires CDelegationMapIsValid(m);
    requires EndPointIsValid(id);
    requires !EmptyKeyRange(newkr);
    requires !KeyRangeContains(newkr, KeyPlus(k));
    requires left_index == CDM_IndexForKey(m, newkr.klo) as int;
    requires right_index == CDM_IndexForKey(m, newkr.khi) as int;
    requires 0 <= new_index <= |m.lows|;
    requires |new_left| == new_index;
    requires new_left == m.lows[..new_index];
    requires new_right == if newkr.khi.KeyInf? then [] else [Mapping(newkr.khi, m.lows[right_index].id)] + m.lows[right_index+1..];
    requires m' == CDelegationMap(new_left + [Mapping(newkr.klo, id)] + new_right);
    requires CDelegationMapIsValid(m');
    requires var k_index := CDM_IndexForKey(m', KeyPlus(k)) as int;
             k_index > new_index + 1;
    ensures  AbstractifyCDelegationMapToDelegationMap(m')[k] == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id))[k];

{

    var rm  := AbstractifyCDelegationMapToDelegationMap(m);
    var rm' := AbstractifyCDelegationMapToDelegationMap(m');
    var updated_rm := UpdateDelegationMap(rm, newkr, AbstractifyEndPointToNodeIdentity(id));
    var k_index := CDM_IndexForKey(m', KeyPlus(k)) as int;

    CDelegationMapIsSortedExtension(m);
    CDelegationMapIsSortedExtension(m');

    assert !newkr.khi.KeyInf?;
    var cr := CDM_IndexToKeyRange(m', k_index as int);
    assert KeyRangeContains(cr, KeyPlus(k));
    assert m'.lows == m.lows[..new_index] + [Mapping(newkr.klo, id)] + [Mapping(newkr.khi, m.lows[right_index].id)] + m.lows[right_index+1..];

    assert {:split_here} true;

    assert |m.lows[..new_index]| == new_index == new_index;
    assert |m.lows[..new_index] + [Mapping(newkr.klo, id)] + [Mapping(newkr.khi, m.lows[right_index].id)]| == new_index + 2;
    if |m.lows[right_index+1..]| > k_index as int - new_index - 2 {
        assert {:split_here} true;
        SequenceIndexingHelper(m.lows[..new_index], [Mapping(newkr.klo, id)], [Mapping(newkr.khi, m.lows[right_index].id)], m.lows[right_index+1..], m'.lows, k_index);
        assert m'.lows[k_index] == m.lows[right_index+1..][k_index-new_index - 2];
    } else {
        assert false;
    }

    assert cr.klo == m'.lows[k_index].klo == m.lows[right_index+1..][k_index-new_index-2].klo;
    var offset_index := right_index+1 + k_index-new_index-2;
    calc {
        m'.lows[k_index];
        m.lows[right_index+1..|m.lows|][k_index-new_index-2];
            { assert m.lows[right_index+1..|m.lows|][k_index-new_index-2] == m.lows[right_index+1 + k_index-new_index-2];}
        m.lows[right_index+1 + k_index-new_index-2];
        m.lows[offset_index];
    }
    assert KeyPlusLe(m.lows[offset_index].klo, KeyPlus(k));
    var offplusone := offset_index + 1;
    if offplusone < |m.lows| {
        assert offplusone < |m.lows|;
        assert KeyPlusLt(KeyPlus(k), m.lows[offplusone].klo);
    }

    CDM_Partitioned(m, KeyPlus(k), offset_index);
    assert CDM_IndexForKey(m, KeyPlus(k)) as int == offset_index;
    //var i :| 0 <= i < |m.lows| && m.lows[i].klo == cr.klo;
    assert rm'[k] == rm[k];
}


lemma {:timeLimitMultiplier 4} UpdateCDelegationMap_RHS(m:CDelegationMap, newkr:KeyRange, id:EndPoint, m':CDelegationMap,
                               left_index:int, right_index:int, new_left:seq<Mapping>, new_right:seq<Mapping>,
                               k:Key, new_index:int)
    requires CDelegationMapIsValid(m);
    requires EndPointIsValid(id);
    requires !EmptyKeyRange(newkr);
    requires !KeyRangeContains(newkr, KeyPlus(k));
    requires left_index == CDM_IndexForKey(m, newkr.klo) as int;
    requires right_index == CDM_IndexForKey(m, newkr.khi) as int;
    requires 0 <= new_index <= |m.lows|;
    requires |new_left| == new_index;
    requires new_left == m.lows[..new_index];
    requires new_right == if newkr.khi.KeyInf? then [] else [Mapping(newkr.khi, m.lows[right_index].id)] + m.lows[right_index+1..];
    requires m' == CDelegationMap(new_left + [Mapping(newkr.klo, id)] + new_right);
    requires CDelegationMapIsValid(m');
    requires var k_index := CDM_IndexForKey(m', KeyPlus(k)) as int;
             k_index > new_index;
    ensures  AbstractifyCDelegationMapToDelegationMap(m')[k] == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id))[k];
{
    var rm  := AbstractifyCDelegationMapToDelegationMap(m);
    var rm' := AbstractifyCDelegationMapToDelegationMap(m');
    var updated_rm := UpdateDelegationMap(rm, newkr, AbstractifyEndPointToNodeIdentity(id));
    var k_index := CDM_IndexForKey(m', KeyPlus(k)) as int;

    CDelegationMapIsSortedExtension(m);
    CDelegationMapIsSortedExtension(m');

    assert !newkr.khi.KeyInf?;

    if k_index == new_index + 1 {
        assert CDM_IndexToKeyRange(m', k_index as int).klo == newkr.khi;
        assert rm'[k] == AbstractifyEndPointToNodeIdentity(m.lows[right_index].id);
        assert KeyPlusLe(m.lows[right_index].klo, newkr.khi);
        assert KeyPlusLe(newkr.khi, KeyPlus(k));
        KeyPlusTransitivity(m.lows[right_index].klo, newkr.khi, KeyPlus(k));
        assert KeyPlusLe(m.lows[right_index].klo, KeyPlus(k));
        if |m.lows| > right_index + 1 {
            assert KeyPlusLt(KeyPlus(k), m.lows[right_index+1].klo);
            assert KeyRangeContains(CDM_IndexToKeyRange(m, right_index), KeyPlus(k));
            CDM_Partitioned(m, KeyPlus(k), right_index);
        } else if |m.lows| == right_index + 1 {
            assert rm'[k] == AbstractifyEndPointToNodeIdentity(m.lows[right_index].id);
            assert KeyPlusLe(m.lows[right_index].klo, newkr.khi);
            assert KeyPlusLe(newkr.khi, KeyPlus(k));
            KeyPlusTransitivity(m.lows[right_index].klo, newkr.khi, KeyPlus(k));// ==> m.lows[right_index] <= k
            assert KeyRangeContains(CDM_IndexToKeyRange(m, right_index), KeyPlus(k));
            CDM_Partitioned(m, KeyPlus(k), right_index);
            assert rm[k] == AbstractifyEndPointToNodeIdentity(m.lows[right_index].id);
            assert rm'[k] == rm[k];
        } else {
            assert false;
        }
    } else {
        assert k_index > new_index + 1;
        UpdateCDelegationMap_RHS_Helper(m, newkr, id, m', left_index, right_index, new_left, new_right, k, new_index);
    }
    assert AbstractifyCDelegationMapToDelegationMap(m')[k] == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id))[k];
}

lemma {:timeLimitMultiplier 4} {:induction false} UpdateCDelegationMap_Part2(m:CDelegationMap, newkr:KeyRange, id:EndPoint, m':CDelegationMap,
                                 left_index:int, right_index:int, new_left:seq<Mapping>, new_right:seq<Mapping>)
    requires CDelegationMapIsValid(m);
    requires EndPointIsValid(id);
    requires !EmptyKeyRange(newkr);
    requires left_index == CDM_IndexForKey(m, newkr.klo) as int;
    requires right_index == CDM_IndexForKey(m, newkr.khi) as int;
    requires new_left == m.lows[..left_index];
    requires m.lows[left_index].klo == newkr.klo;
    requires !(left_index == 0 && !newkr.klo.KeyZero?);  // left_index != 0 || newkr.klo.KeyZero
    requires new_right == if newkr.khi.KeyInf? then [] else [Mapping(newkr.khi, m.lows[right_index].id)] + m.lows[right_index+1..];
    requires m' == CDelegationMap(new_left + [Mapping(newkr.klo, id)] + new_right);
    requires CDelegationMapIsValid(m');
    ensures  AbstractifyCDelegationMapToDelegationMap(m') == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id));
{
    var rm  := AbstractifyCDelegationMapToDelegationMap(m);
    var rm' := AbstractifyCDelegationMapToDelegationMap(m');
    var updated_rm := UpdateDelegationMap(rm, newkr, AbstractifyEndPointToNodeIdentity(id));

    forall k:Key 
        ensures k in rm' <==> k in updated_rm;
    { 
    }

    forall k:Key 
        ensures rm'[k] == updated_rm[k];
    { 
        CDelegationMapIsSortedExtension(m);
        CDelegationMapIsSortedExtension(m');

        var k_index := CDM_IndexForKey(m', KeyPlus(k)) as int;
        if KeyRangeContains(newkr, KeyPlus(k)) {
            if newkr.klo.KeyZero? {
                assert KeyPlusLe(newkr.klo, m.lows[0].klo);
                if |m.lows| > 1 {
                    assert KeyPlusLt(newkr.klo, m.lows[1].klo);
                }
                CDM_Partitioned(m, newkr.klo, 0);
                assert new_left == [];
                CDM_Partitioned(m', KeyPlus(k), 0);
                assert k_index == 0;
                assert rm'[k] == AbstractifyEndPointToNodeIdentity(id);
                assert rm'[k] == updated_rm[k];
            } else {
                assert m'.lows[left_index] == Mapping(newkr.klo, id);
                assert KeyRangeContains(CDM_IndexToKeyRange(m', left_index), KeyPlus(k));
                CDM_Partitioned(m', KeyPlus(k), left_index);
                assert rm'[k] == AbstractifyEndPointToNodeIdentity(id);
                assert rm'[k] == updated_rm[k];
            }
        } else {
            KeyPlusAntisymmetry(KeyPlus(k), newkr.khi);
            assert !KeyPlusLt(KeyPlus(k), newkr.khi) ==> KeyPlusLe(newkr.khi, KeyPlus(k));
            KeyPlusAntisymmetry(newkr.klo, KeyPlus(k));
            assert !KeyPlusLe(newkr.klo, KeyPlus(k)) ==> KeyPlusLt(KeyPlus(k), newkr.klo);
            assert KeyPlusLt(KeyPlus(k), newkr.klo) || KeyPlusLe(newkr.khi, KeyPlus(k));  // From !KeyRangeContains(newkr, k)
            
            assert m'.lows[left_index] == Mapping(newkr.klo, id);

            if k_index < left_index {
                assert m'.lows[k_index] == m.lows[..left_index][k_index] == m.lows[k_index];
                if k_index < left_index - 1 {
                    assert KeyRangeContains(CDM_IndexToKeyRange(m', k_index), KeyPlus(k));
                    CDM_Partitioned(m', KeyPlus(k), k_index);
                    assert KeyRangeContains(CDM_IndexToKeyRange(m, k_index), KeyPlus(k));
                    CDM_Partitioned(m, KeyPlus(k), k_index);
                    assert rm'[k] == updated_rm[k];
                } else {    // k_index == left_index - 1
                    assert KeyRangeContains(CDM_IndexToKeyRange(m', k_index), KeyPlus(k));
                    //CDM_Partitioned(m', KeyPlus(k), k_index);
                    // ==> m.lows[k_index].klo <= k < newkr.klo
                    assert KeyPlusLe(m.lows[k_index].klo, KeyPlus(k));
                    assert KeyPlusLt(KeyPlus(k), newkr.klo);
                    assert KeyPlusLt(KeyPlus(k), m.lows[left_index].klo);

                    var range := CDM_IndexToKeyRange(m, k_index);
                    assert range == CDM_IndexRangeToKeyRange(m, k_index, k_index);
                    assert range == KeyRange(m.lows[k_index].klo, CDM_IndexToNextKeyBoundary(m, k_index));
                    assert range == KeyRange(m.lows[k_index].klo, if k_index < |m.lows| - 1 then m.lows[k_index+1].klo else KeyInf());
                    assert range == KeyRange(m.lows[k_index].klo, m.lows[k_index+1].klo);
                    assert k_index == left_index - 1;
                    assert KeyPlusLt(KeyPlus(k), m.lows[left_index].klo);
                    assert left_index == k_index + 1;
                    assert KeyPlusLt(KeyPlus(k), m.lows[k_index+1].klo);
                    assert KeyPlusLe(range.klo, KeyPlus(k));
                    assert KeyPlusLt(KeyPlus(k), range.khi);
                    assert KeyRangeContains(range, KeyPlus(k));
                    CDM_Partitioned(m, KeyPlus(k), k_index);
                    assert CDM_IndexForKey(m, KeyPlus(k)) as int == k_index;
                    assert rm'[k] == AbstractifyEndPointToNodeIdentity(m.lows[k_index].id);

                    assert rm'[k] == updated_rm[k];
                }
            } else {
                var new_index := left_index;  // Index of the new mapping, Mapping(newkr.klo, id)
                assert k_index > new_index;

                UpdateCDelegationMap_RHS(m, newkr, id, m', left_index, right_index, new_left, new_right, k, left_index);

                assert rm'[k] == updated_rm[k];
            }
        }
    }
    lemma_UpdateCDelegationMap_Part2_Helper(m, m', newkr, id);
    assert AbstractifyCDelegationMapToDelegationMap(m') == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id));
}


method {:induction false} {:timeLimitMultiplier 4} UpdateCDelegationMap(m:CDelegationMap, newkr:KeyRange, id:EndPoint) returns (ok:bool, m':CDelegationMap)
    requires CDelegationMapIsValid(m);
    requires EndPointIsValid(id);
    requires !EmptyKeyRange(newkr);
    ensures |m.lows| as uint64 < 0xFFFF_FFFF_FFFF_FFFF - 2 ==> ok == true;
    ensures  ok ==> CDelegationMapIsValid(m');
    ensures  ok ==> AbstractifyCDelegationMapToDelegationMap(m') == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, AbstractifyEndPointToNodeIdentity(id));
    ensures ok ==> (|m.lows| as uint64 < 0xFFFF_FFFF_FFFF_FFFF - 2) && (|m'.lows| as uint64 <= |m.lows| as uint64 + 2);
{
    if |m.lows| as uint64 >= 0xFFFF_FFFF_FFFF_FFFF - 2 {
        ok := false;
        return;
    }

    ok := true;

    // !Empty implies:
    assert !newkr.klo.KeyInf?;
    assert !newkr.khi.KeyZero?;

    var left_index  := CDM_IndexForKey(m, newkr.klo);
    var right_index := CDM_IndexForKey(m, newkr.khi);

    CDM_IndexForKey_Ordering(m);
    KeyPlusAntisymmetry(newkr.klo, newkr.khi);
    assert left_index <= right_index;

    var new_left := m.lows[..left_index];
    if m.lows[left_index].klo != newkr.klo {
        // We need to keep the left_index-th mapping, since it contains the bottom of the range, before we get to newkr.klo
        new_left := m.lows[..left_index+1];
    }

    var new_right; 
    if newkr.khi.KeyInf? {
        // We're taking all of the keys from newkr.klo onwards
        new_right := [];
    } else {
        // We still need to map the portion of the range above newkr.khi but inside m.lows[right_index]
        new_right := [Mapping(newkr.khi, m.lows[right_index].id)] + m.lows[right_index+1..];
        assert KeyPlusLt(newkr.klo, newkr.khi);
        if right_index as int + 1 < |m.lows| {
            assert KeyPlusLt(newkr.khi, m.lows[right_index+1].klo);
        }
    }

    m' := CDelegationMap(
          new_left
        + [Mapping(newkr.klo, id)]
        + new_right);

    CDelegationMapIsSortedExtension(m);

    assert {:split_here} true;

    forall i | 0 <= i < |m'.lows|-1
        ensures KeyPlusLt(m'.lows[i].klo, m'.lows[i+1].klo);
    {
        if i < |new_left| {
            assert m'.lows[i] == new_left[i];
            if i == |new_left| - 1 {
                assert m'.lows[i+1].klo == Mapping(newkr.klo, id).klo;
                if m.lows[left_index].klo != newkr.klo {
                    assert KeyPlusLt(m'.lows[i].klo, m'.lows[i+1].klo);
                } else {
                    assert i == left_index as int - 1;

                    assert m'.lows[i].klo == m.lows[i].klo;
                    assert KeyPlusLe(m.lows[i + 1].klo, newkr.klo);
                    assert KeyPlusLt(m.lows[i].klo, m.lows[i + 1].klo);
                    KeyPlusTransitivity(m.lows[i].klo, m.lows[i+1].klo, newkr.klo);

                    assert KeyPlusLt(m'.lows[i].klo, Mapping(newkr.klo, id).klo);
                    assert KeyPlusLt(m'.lows[i].klo, m'.lows[i+1].klo);
                }
            } else {
                assert KeyPlusLt(m'.lows[i].klo, m'.lows[i+1].klo);
            }
        } else if i == |new_left| {
            assert m'.lows[i].klo == newkr.klo;
            assert KeyPlusLt(m'.lows[i].klo, m'.lows[i+1].klo);
        } else {
            if newkr.khi.KeyInf? {
            } else {
                if i == |new_left| + 1 {
                    assert m'.lows[i] == Mapping(newkr.khi, m.lows[right_index].id);
                    assert m'.lows[i].klo == newkr.khi;
                    assert m'.lows[i+1].klo == m.lows[right_index+1].klo;
                } else {
                    SequenceIndexingHelper(new_left, [Mapping(newkr.klo, id)], [Mapping(newkr.khi, m.lows[right_index].id)], m.lows[right_index+1..], m'.lows, i);
                }
            }
            //assert KeyPlusLt(m'.lows[i].klo, m'.lows[i+1].klo);
        }
    }
    assert CDelegationMapIsSorted(m);
    assert KeyPlusLt(m.lows[|m.lows|-1].klo, KeyInf());
    assert KeyPlusLt(m'.lows[|m'.lows|-1].klo, KeyInf());

    assert CDelegationMapIsSorted(m'); 
    
    if left_index > 0 {
        assert |m'.lows| > 0;
        assert m'.lows[0].klo == KeyZero();
        //assert AbstractifyCDelegationMapToDelegationMap(m') == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, id);
    } else {
        assert m.lows[0].klo == KeyZero();
        if newkr.klo != KeyZero() {
            assert new_left == m.lows[..1];
            assert m'.lows[0].klo == m.lows[0].klo;
        } else {
            assert m'.lows[0].klo == newkr.klo;
        }
        assert m'.lows[0].klo == KeyZero();
        //assert AbstractifyCDelegationMapToDelegationMap(m') == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(m), newkr, id);
    }

    if m.lows[left_index].klo != newkr.klo {
        UpdateCDelegationMap_Part1(m, newkr, id, m', left_index as int, right_index as int, new_left, new_right);
    } else {
        UpdateCDelegationMap_Part2(m, newkr, id, m', left_index as int, right_index as int, new_left, new_right);
    }
}


lemma lemma_CDM_NoLowsAreInfinite(m:CDelegationMap)
    requires CDelegationMapIsValid(m);
    ensures  forall i :: 0 <= i < |m.lows| ==> !m.lows[i].klo.KeyInf?;
{
    forall i | 0 <= i < |m.lows|
        ensures !m.lows[i].klo.KeyInf?;
    {
        if m.lows[i].klo.KeyInf? {
            CDelegationMapIsSortedExtension(m);
            var last := |m.lows| - 1;
            if i == last {
                assert KeyPlusLt(m.lows[i].klo, KeyInf());
            } else {
                assert KeyPlusLt(m.lows[i].klo, m.lows[last].klo);
                KeyPlusTransitivity(m.lows[i].klo, m.lows[last].klo, KeyInf());
            }
            KeyPlusAntisymmetry(m.lows[i].klo, KeyInf());
            assert false;
        }
    }
}

method CDM_Defragment(m:CDelegationMap) returns (m':CDelegationMap)
    requires CDelegationMapIsValid(m);
    ensures  CDelegationMapIsValid(m');
    ensures  AbstractifyCDelegationMapToDelegationMap(m) == AbstractifyCDelegationMapToDelegationMap(m');
    ensures  |m'.lows| >= 2 && m'.lows[1].klo.KeyPlus? ==> m'.lows[1].klo.k != KeyMin();
{
    if |m.lows| as uint64 < 2 || m.lows[1].klo != KeyPlus(KeyMin()) {
        return m;
    }

    if |m.lows| >= 3 {
        CDelegationMapIsSortedExtension_recursive(m, 1, 2);
        KeyPlusAntisymmetry(m.lows[1].klo, m.lows[2].klo);
        assert m.lows[2].klo != KeyPlus(KeyMin());
    }

    var new_lows := [Mapping(KeyZero(), m.lows[1].id)] + m.lows[2..];
    m' := CDelegationMap(new_lows);

    // Prove the third ensures
    lemma_CDM_NoLowsAreInfinite(m);

    // Prove sorted to prove IsValid
    assert CDelegationMapBoundedSize(m');
    forall i | 0 <= i < |m'.lows| - 1
        ensures KeyPlusLt(m'.lows[i].klo, m'.lows[i+1].klo);
    {
        if i == 0 {
            assert KeyPlusLt(m.lows[0].klo, m.lows[1].klo);
        } else {
            assert m'.lows[i]   == m.lows[2..][i-1] == m.lows[1+i];
            assert m'.lows[i+1] == m.lows[2..][i]   == m.lows[2+i];
            CDelegationMapIsSortedExtension_recursive(m, 1+i, 2+i);
            assert KeyPlusLt(m.lows[1+i].klo, m.lows[2+i].klo);
        }
    }
    assert KeyPlusLt(m'.lows[|m'.lows|-1].klo, KeyInf());
    assert CDelegationMapIsSorted(m');
    
    // Prove equivalent refinements
    forall k:Key 
        ensures m.lows[CDM_IndexForKey(m,KeyPlus(k))].id == m'.lows[CDM_IndexForKey(m',KeyPlus(k))].id;
    {
        ghost var kp := KeyPlus(k);
        ghost var k_index  := CDM_IndexForKey(m,  kp) as int;
        ghost var k_index' := CDM_IndexForKey(m', kp) as int;
        if KeyRangeContains(CDM_IndexToKeyRange(m, 0), kp) {
            assert KeyPlusLt(kp, m.lows[1].klo);
            assert KeyPlusLt(kp, KeyPlus(KeyMin()));
            KeyPlusAntisymmetry(kp, KeyPlus(KeyMin()));
            assert false;
        }
        assert k_index >= 1;
    
        if k_index' == 0 {
            if k_index == 1 {
                assert m'.lows[0].id == m.lows[1].id;
            } else {
                assert KeyPlusLt(kp, m'.lows[1].klo);
                assert KeyPlusLt(kp, m.lows[2].klo);
                if 2 < k_index {
                    CDelegationMapIsSortedExtension_recursive(m, 2, k_index);
                }
                assert KeyPlusLe(m.lows[2].klo, m.lows[k_index].klo);
                KeyPlusTransitivity(kp, m.lows[2].klo, m.lows[k_index].klo);    // ==> kp < m.lows[k_index]
                // But we also know:
                assert KeyPlusLe(m.lows[k_index].klo, kp);
                KeyPlusAntisymmetry(m.lows[k_index].klo, kp);   // Contradiction!
                assert false;
            }
        } else {
            if k_index == k_index' + 1 {
                assert m'.lows[k_index'] == m.lows[k_index];
            } else {
                assert m'.lows[k_index'] == m.lows[k_index' + 1];
                assert KeyRangeContains(CDM_IndexToKeyRange(m, k_index), kp);
                assert KeyRangeContains(CDM_IndexToKeyRange(m, k_index' + 1), kp);
                CDM_Partitioned(m, kp, k_index);
                assert false;
            }
        } 
    }
    lemma_CDM_Defragment_equivalence(m, m');
}


lemma lemma_CDM_Defragment_equivalence(m:CDelegationMap, m':CDelegationMap)
    requires CDelegationMapIsValid(m);
    requires  CDelegationMapIsValid(m');
    requires forall k:Key :: true ==> m.lows[CDM_IndexForKey(m,KeyPlus(k))].id == m'.lows[CDM_IndexForKey(m',KeyPlus(k))].id;
    ensures  AbstractifyCDelegationMapToDelegationMap(m) == AbstractifyCDelegationMapToDelegationMap(m');
{
}



lemma CDM_IndexForKey_Ordering_specific(m:CDelegationMap, k1:KeyPlus, k2:KeyPlus)
    requires CDelegationMapIsValid(m);
    requires KeyPlusLe(k1, k2);
    ensures  CDM_IndexForKey(m, k1) <= CDM_IndexForKey(m, k2);
{
    CDM_IndexForKey_Ordering(m);
}

function min(x:int, y:int) : int { if x < y then x else y }

predicate InBounds(i:int, low:int, high:int, len:int)
{
    low <= i < min(high, len)
}

method DelegateForKeyRangeIsHostImpl(m:CDelegationMap, kr:KeyRange, id:EndPoint) returns (b:bool)
    requires CDelegationMapIsValid(m);
    requires EndPointIsAbstractable(id);
    ensures  b == DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(m), kr, AbstractifyEndPointToNodeIdentity(id));
{
    if EmptyKeyRange(kr) {
        b := true;
        forall k | KeyRangeContains(kr, KeyPlus(k))
            ensures false;
        {
            assert KeyPlusLe(kr.klo, KeyPlus(k));
            assert KeyPlusLt(KeyPlus(k), kr.khi);
            assert KeyPlusLe(kr.khi, kr.klo);
            KeyPlusTransitivity(kr.klo, KeyPlus(k), kr.khi);
            assert KeyPlusLt(kr.klo, kr.khi);
            KeyPlusAntisymmetry(kr.klo, kr.khi);
        }
        return;
    } 

    var k_min := KeyMin();
    if kr.klo.KeyZero? && kr.khi == KeyPlus(k_min) {
        forall k | KeyRangeContains(kr, KeyPlus(k))
            ensures false;
        {
            assert KeyPlusLe(kr.khi, KeyPlus(k));
            KeyPlusAntisymmetry(kr.khi, KeyPlus(k));
        }
       return true;
    }

    var m' := CDM_Defragment(m);

    var lo_index := CDM_IndexForKey(m', kr.klo);
    var hi_index := CDM_IndexForKey(m', kr.khi);

    forall () ensures lo_index <= hi_index;
    {
        KeyPlusAntisymmetry(kr.klo, kr.khi);
        CDM_IndexForKey_Ordering_specific(m', kr.klo, kr.khi);
    }

    var index := lo_index;
    ghost var witness_key := kr.klo;
    assert KeyPlusLe(kr.klo, witness_key);
    KeyPlusAntisymmetry(kr.klo, kr.khi);    // ==>
    assert KeyPlusLt(witness_key, kr.khi);
    while index <= hi_index 
        invariant lo_index <= index <= hi_index + 1;
        invariant forall i {:trigger InBounds(i, lo_index as int, index as int, |m'.lows|)} :: 
                    InBounds(i, lo_index as int, index as int, |m'.lows|) ==> m'.lows[i].id == id;
        invariant !witness_key.KeyInf?;
        invariant KeyRangeContains(kr, witness_key);
        invariant index <= hi_index ==> CDM_IndexForKey(m', witness_key) == index;
    {
        if m'.lows[index].id != id {
            b := false;

            forall () ensures AbstractifyEndPointToNodeIdentity(m'.lows[index].id) != AbstractifyEndPointToNodeIdentity(id) 
            {
                if AbstractifyEndPointToNodeIdentity(m'.lows[index].id) == AbstractifyEndPointToNodeIdentity(id) {
                   lemma_AbstractifyEndPointToNodeIdentity_injective(m'.lows[index].id, id);
                   assert false;
                }
            }
            if !witness_key.KeyZero? {
                assert !DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(m'), kr, AbstractifyEndPointToNodeIdentity(id));
            } else {
                assert kr.klo.KeyZero?;
                assert !kr.khi.KeyZero? && kr.khi != KeyPlus(k_min);
                forall () ensures index == 0;
                {
                    assert KeyRangeContains(CDM_IndexToKeyRange(m', 0), witness_key);
                    CDM_Partitioned(m', witness_key, 0);
                    if index != 0 {
                        assert CDM_IndexForKey(m', witness_key) != 0;
                        assert KeyRangeContains(CDM_IndexToKeyRange(m', index as int), witness_key);
                        assert false;
                    }
                    assert index == 0;  // Because witness_key is 0, it can only be contained from below by the 0th mapping
                }
                if |m'.lows| == 1 {
                    assert KeyRangeContains(kr, KeyPlus(k_min));
                    assert AbstractifyCDelegationMapToDelegationMap(m')[k_min] != AbstractifyEndPointToNodeIdentity(id);
                } else {
                    assert m'.lows[1].klo != KeyPlus(k_min);
                    assert KeyPlusLt(KeyPlus(k_min), m'.lows[1].klo);
                    assert KeyRangeContains(kr, KeyPlus(k_min));
                    assert KeyRangeContains(CDM_IndexToKeyRange(m', 0), KeyPlus(k_min));
                    calc ==> {
                        true;
                            { CDM_Partitioned(m', KeyPlus(k_min), 0); }
                        CDM_IndexForKey(m', KeyPlus(k_min)) == 0; 
                    }
                    assert AbstractifyCDelegationMapToDelegationMap(m')[k_min] != AbstractifyEndPointToNodeIdentity(id);
                }
                assert b == DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(m'), kr, AbstractifyEndPointToNodeIdentity(id));
            }
            return;
        }
        ghost var old_index := index;
        index := index + 1;
        if index <= hi_index {
            ghost var old_witness := witness_key;
            witness_key := m'.lows[index].klo;
            lemma_CDM_NoLowsAreInfinite(m');
            //CDM_IndexForKey_Ordering_specific(m');

            assert KeyPlusLe(kr.klo, old_witness);
            assert CDM_IndexForKey(m', old_witness) == old_index;
            assert KeyPlusLt(old_witness, m'.lows[old_index + 1].klo);
            assert KeyPlusLe(m'.lows[old_index+1].klo, witness_key);
            KeyPlusTransitivity(kr.klo, old_witness, m'.lows[old_index + 1].klo);
            KeyPlusTransitivity(kr.klo, m'.lows[old_index + 1].klo, witness_key);
            assert KeyPlusLe(kr.klo, witness_key);

            if index < hi_index {
                assert KeyPlusLt(witness_key, CDM_IndexToKeyRange(m', index as int).khi);
                CDM_KeyRangesAreOrdered(m', index as int, hi_index as int);
                KeyPlusTransitivity(witness_key, CDM_IndexToKeyRange(m', index as int).khi, m'.lows[hi_index].klo);
                assert KeyPlusLt(witness_key, m'.lows[hi_index].klo);
                assert KeyPlusLe(m'.lows[hi_index].klo, kr.khi);
                KeyPlusTransitivity(witness_key, m'.lows[hi_index].klo, kr.khi);
                assert KeyPlusLt(witness_key, kr.khi);
                assert KeyRangeContains(kr, witness_key);
            } else {
                if kr.khi != m'.lows[index].klo {
                    assert KeyRangeContains(kr, witness_key);
                } else {
                    forall k | KeyRangeContains(kr, KeyPlus(k))
                        ensures AbstractifyCDelegationMapToDelegationMap(m')[k] == AbstractifyEndPointToNodeIdentity(id);
                    {
                        assert KeyPlusLe(kr.klo, KeyPlus(k));
                        assert KeyPlusLt(KeyPlus(k), kr.khi);
                        assert KeyPlusLe(KeyPlus(k), kr.khi);
                        ghost var k_index := CDM_IndexForKey(m', KeyPlus(k));
                        CDM_IndexForKey_Ordering_specific(m', kr.klo, KeyPlus(k));
                        CDM_IndexForKey_Ordering_specific(m', KeyPlus(k), kr.khi);
                        assert lo_index as int <= k_index as int <= hi_index as int < |m'.lows|;
                        if k_index == hi_index {
                            assert KeyPlusLe(kr.khi, KeyPlus(k));
                            KeyPlusAntisymmetry(kr.khi, KeyPlus(k));
                            assert false;
                        }
                        assert InBounds(k_index as int, lo_index as int, hi_index as int, |m'.lows|);
                        if k_index < old_index {
                            assert InBounds(k_index as int, lo_index as int, old_index as int, |m'.lows|);
                            assert m'.lows[k_index].id == id;
                        } else {
                            assert m'.lows[k_index].id == id;
                        }
                    }

                    return true;
                }
            }

            assert KeyRangeContains(CDM_IndexToKeyRange(m', index as int), witness_key);
            CDM_Partitioned(m', witness_key, index as int);
            assert CDM_IndexForKey(m', witness_key) == index;
        }
        forall i {:trigger InBounds(i, lo_index as int, index as int, |m'.lows|)} | 
                 InBounds(i, lo_index as int, index as int, |m'.lows|)
            ensures m'.lows[i].id == id;
        {
            if i < old_index as int {
                assert InBounds(i, lo_index as int, old_index as int, |m'.lows|) ==> m'.lows[i].id == id;
            } else {
            }
        }

    }

    forall k | KeyRangeContains(kr, KeyPlus(k))
        ensures AbstractifyCDelegationMapToDelegationMap(m')[k] == AbstractifyEndPointToNodeIdentity(id);
    {
        assert KeyPlusLe(kr.klo, KeyPlus(k));
        assert KeyPlusLt(KeyPlus(k), kr.khi);
        assert KeyPlusLe(KeyPlus(k), kr.khi);
        ghost var k_index := CDM_IndexForKey(m', KeyPlus(k));
        CDM_IndexForKey_Ordering_specific(m', kr.klo, KeyPlus(k));
        CDM_IndexForKey_Ordering_specific(m', KeyPlus(k), kr.khi);
        assert lo_index as int <= k_index as int <= hi_index as int < |m'.lows|;
        assert InBounds(k_index as int, lo_index as int, index as int, |m'.lows|);
        assert m'.lows[k_index].id == id;
    }

    b := true;
    return;
}

}