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

/************************** AutoMan Translation ************************/

type CDelegationMap = map<Key, EndPoint>

	predicate CDelegationMapIsAbstractable(s: CDelegationMap) 
	{
		(forall i :: i in s ==> KeyIsAbstractable(i) && EndPointIsAbstractable(s[i]))
	}

	predicate CDelegationMapIsValid(s: CDelegationMap) 
	{
		CDelegationMapIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> KeyIsValid(i) && EndPointIsValid(s[i]))
	}

	function AbstractifyCDelegationMapToDelegationMap(s: CDelegationMap) : DelegationMap 
		requires CDelegationMapIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyKeyToKey, AbstractifyEndPointToNodeIdentity, AbstractifyKeyToKey)
	}


function method CDelegationMapComplete(dm: CDelegationMap) : bool 
    requires CDelegationMapIsValid(dm)
    // ensures CDelegationMapComplete(dm) == DelegationMapComplete(AbstractifyCDelegationMapToDelegationMap(dm))
{
    (forall k :: k in dm)
}

function method CDelegationMapHasSameKeys(dm1: CDelegationMap, dm2: CDelegationMap) : bool 
    requires CDelegationMapIsValid(dm1)
    requires CDelegationMapIsValid(dm2)
    ensures CDelegationMapHasSameKeys(dm1, dm2) == DelegationMapHasSameKeys(AbstractifyCDelegationMapToDelegationMap(dm1), AbstractifyCDelegationMapToDelegationMap(dm2))
{
    (forall k :: k in dm1 <==> k in dm2)
}

function method CUpdateDelegationMap(dm: CDelegationMap, newkr: KeyRange, host: EndPoint) : CDelegationMap 
    requires CDelegationMapIsValid(dm)
    requires KeyRangeIsValid(newkr)
    requires EndPointIsValid(host)
    /** Manually Added */
    ensures CDelegationMapIsValid(CUpdateDelegationMap(dm, newkr, host))

    ensures CDelegationMapHasSameKeys(dm, CUpdateDelegationMap(dm, newkr, host))
    ensures (forall k :: k in dm ==> CUpdateDelegationMap(dm, newkr, host)[k] == if KeyRangeContains(newkr, KeyPlus(k)) then host else dm[k])
    ensures CUpdateDelegationMap(dm, newkr, host) == UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(dm), newkr, AbstractifyEndPointToNodeIdentity(host))
{
    map k | k in dm :: if KeyRangeContains(newkr, KeyPlus(k)) then host else dm[k]
    // [Printer for ... hasn't been implemented.]
}

function method CDelegateForKeyRangeIsHost(dm: CDelegationMap, kr: KeyRange, id: EndPoint) : bool 
    requires CDelegationMapIsValid(dm)
    requires KeyRangeIsValid(kr)
    requires EndPointIsValid(id)
    ensures CDelegateForKeyRangeIsHost(dm, kr, id) == DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(dm), kr, AbstractifyEndPointToNodeIdentity(id))
{
    (forall k :: k in dm && KeyRangeContains(kr, KeyPlus(k)) ==> dm[k] == id)
}

function method CDelegationMapsAreEqualUpToKey(adm: CDelegationMap, bdm: CDelegationMap, khi: KeyPlus) : bool 
    requires CDelegationMapIsValid(adm)
    requires CDelegationMapIsValid(bdm)
    requires KeyPlusIsValid(khi)
    requires CDelegationMapHasSameKeys(adm, bdm)
    ensures CDelegationMapsAreEqualUpToKey(adm, bdm, khi) == DelegationMapsAreEqualUpToKey(AbstractifyCDelegationMapToDelegationMap(adm), AbstractifyCDelegationMapToDelegationMap(bdm), khi)
{
    (forall k :: k in adm && KeyPlusLt(KeyPlus(k), khi) ==> adm[k] == bdm[k])
}

function method CDelegateForKey(dm: CDelegationMap, k: Key) : EndPoint 
    requires CDelegationMapIsValid(dm)
    requires KeyIsValid(k)
    requires k in dm
    ensures CDelegateForKey(dm, k) == DelegateForKey(AbstractifyCDelegationMapToDelegationMap(dm), k)
{
    dm[k]
}

function method CBulkUpdateDomain(h: Hashtable, kr: KeyRange, u: Hashtable) : set<Key> 
    requires HashtableIsValid(h)
    requires KeyRangeIsValid(kr)
    requires HashtableIsValid(u)
    ensures CBulkUpdateDomain(h, kr, u) == BulkUpdateDomain(h, kr, u)
{
    set k | k in mapdomain(h)+mapdomain(u) && (KeyRangeContains(kr, KeyPlus(k)) ==> k in u)
    // [Printer for ... hasn't been implemented.]
}


function method CBulkUpdateHashtable(h: Hashtable, kr: KeyRange, u: Hashtable) : Hashtable 
    requires HashtableIsValid(h)
    requires KeyRangeIsValid(kr)
    requires HashtableIsValid(u)
    ensures CBulkUpdateHashtable(h, kr, u) == BulkUpdateHashtable(h, kr, u)
{
    (map k | k in CBulkUpdateDomain(h, kr, u) :: if k in u then u[k] else h[k])
}

function method CBulkRemoveHashtable(h: Hashtable, kr: KeyRange) : Hashtable 
    requires HashtableIsValid(h)
    requires KeyRangeIsValid(kr)
    ensures CBulkRemoveHashtable(h, kr) == BulkRemoveHashtable(h, kr)
{
    (map k | k in h && !KeyRangeContains(kr, KeyPlus(k)) :: h[k])
}

function method CExtractRange(h: Hashtable, kr: KeyRange) : Hashtable 
    requires HashtableIsValid(h)
    requires KeyRangeIsValid(kr)
    ensures CExtractRange(h, kr) == ExtractRange(h, kr)
{
    (map k | k in h && KeyRangeContains(kr, KeyPlus(k)) :: h[k])
}
/************************** AutoMan Translation End ************************/
// type CDelegationMap = map<Key, EndPoint>

// predicate CDelegationMapIsAbstractable(dm:CDelegationMap)
// {
//     && (forall k :: k in dm ==> KeyIsAbstractable(k) && EndPointIsAbstractable(dm[k]))
// }

// predicate CDelegationMapIsValid(dm:CDelegationMap)
// {
//     && CDelegationMapIsAbstractable(dm)
//     && (forall k :: k in dm ==> KeyIsValid(k) && EndPointIsValid(dm[k]))
// }

// function AbstractifyCDelegationMapToDelegationMap(dm:CDelegationMap) : DelegationMap
//     requires CDelegationMapIsAbstractable(dm)
// {
//     AbstractifyMap(dm, AbstractifyKeyToKey, AbstractifyEndPointToNodeIdentity, RefineKeyToKey)
// }

// predicate method CDelegationMapComplete(dm:CDelegationMap)
//     requires CDelegationMapIsValid(dm)
//     // ensures CDelegationMapComplete(dm) ==> DelegationMapComplete(AbstractifyCDelegationMapToDelegationMap(dm))
// {
//     // ghost var m := AbstractifyCDelegationMapToDelegationMap(dm);
//     // assert forall k :: k in dm ==> AbstractifyKeyToKey(k) in m;
//     // assert 
//     forall k :: k in dm
// }

// predicate method CDelegationMapHasSameKeys(dm1:CDelegationMap, dm2:CDelegationMap)
// {
//     && (forall k :: k in dm1 <==> k in dm2)
// }


// function method CUpdateDelegationMap(dm:CDelegationMap, newkr:KeyRange, host:EndPoint) : CDelegationMap
//     requires CDelegationMapIsValid(dm)
//     requires KeyRangeIsValid(newkr)
//     requires EndPointIsValid(host)
//     ensures CDelegationMapIsValid(CUpdateDelegationMap(dm, newkr, host))
//     ensures CDelegationMapHasSameKeys(dm, CUpdateDelegationMap(dm, newkr, host))
//     ensures  forall k :: k in dm ==> CUpdateDelegationMap(dm, newkr, host)[k] == if KeyRangeContains(newkr, KeyPlus(k)) then host else dm[k];
// {
//     map k | k in dm :: if KeyRangeContains(newkr, KeyPlus(k)) then host else dm[k]
// }

// predicate method CDelegateForKeyRangeIsHost(dm:CDelegationMap, kr:KeyRange, id:EndPoint)
//     requires CDelegationMapIsValid(dm)
//     requires KeyRangeIsValid(kr)
//     requires EndPointIsValid(id)
//     ensures CDelegateForKeyRangeIsHost(dm, kr, id) ==
//             DelegateForKeyRangeIsHost(
//                 AbstractifyCDelegationMapToDelegationMap(dm),
//                 kr,
//                 AbstractifyEndPointToNodeIdentity(id)
//             )
// {
//     forall k :: k in dm && KeyRangeContains(kr, KeyPlus(k)) ==> dm[k] == id
// }

// predicate CDelegationMapsAreEqualUpToKey(adm:CDelegationMap, bdm:CDelegationMap, khi:KeyPlus)
//     requires CDelegationMapIsValid(adm)
//     requires CDelegationMapIsValid(bdm)
//     requires CDelegationMapHasSameKeys(adm, bdm)
//     ensures CDelegationMapsAreEqualUpToKey(adm, bdm, khi) == 
//             DelegationMapsAreEqualUpToKey(
//                 AbstractifyCDelegationMapToDelegationMap(adm),
//                 AbstractifyCDelegationMapToDelegationMap(bdm),
//                 khi
//             )
// {
//     forall k :: k in adm && KeyPlusLt(KeyPlus(k), khi) ==> adm[k] == bdm[k]
// }

// function method CDelegateForKey(dm:CDelegationMap, k:Key) : EndPoint
//     requires CDelegationMapIsValid(dm)
//     requires k in dm
//     ensures var e := CDelegateForKey(dm, k);
//             AbstractifyEndPointToNodeIdentity(e) == 
//             DelegateForKey(
//                 AbstractifyCDelegationMapToDelegationMap(dm),
//                 k
//             )
// {
//     dm[k]
// }

// function method CBulkUpdateDomain(h:Hashtable, kr:KeyRange, u:Hashtable) : set<Key>
//     requires HashtableIsValid(h)
//     requires KeyRangeIsValid(kr)
//     requires HashtableIsValid(u)
//     ensures var s := CBulkUpdateDomain(h,kr,u);
//             s == BulkUpdateDomain(
//                 h,kr,u
//             )
// {
//     // Clumsy heuristically-obviously-finite set construction
//     set k | k in mapdomain(h)+mapdomain(u) && (KeyRangeContains(kr, KeyPlus(k)) ==> k in u)
// }

// function CBulkUpdateHashtable(h:Hashtable, kr:KeyRange, u:Hashtable) : Hashtable
//     requires HashtableIsValid(h)
//     requires KeyRangeIsValid(kr)
//     requires HashtableIsValid(u)
//     ensures var new_h := CBulkUpdateHashtable(h,kr,u);
//             new_h == BulkUpdateHashtable(h,kr,u)
// {
//     map k | k in CBulkUpdateDomain(h, kr, u) :: if (k in u) then u[k] else h[k]
// }

// function CBulkRemoveHashtable(h:Hashtable, kr:KeyRange) : Hashtable 
//     requires HashtableIsValid(h)
//     requires KeyRangeIsValid(kr)
//     ensures var new_h := CBulkRemoveHashtable(h,kr);
//             new_h == BulkRemoveHashtable(h,kr)
// {
//     map k | (k in h && !KeyRangeContains(kr, KeyPlus(k))) :: h[k]
// }

// function CExtractRange(h:Hashtable, kr:KeyRange) : Hashtable
//     requires HashtableIsValid(h)
//     requires KeyRangeIsValid(kr)
//     ensures var new_h := CExtractRange(h,kr);
//             new_h == ExtractRange(h,kr)
// {
//     map k | (k in h && KeyRangeContains(kr, KeyPlus(k))) :: h[k]
// }

}