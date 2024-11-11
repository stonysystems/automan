include ""


module Impl_SHT__Delegations_i 
{
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
		AbstractifyMap(s, AbstractifyKeyToKey, AbstractifyNodeIdentityToEndPoint, AbstractifyKeyToKey)
	}

	function method CDelegationMapComplete(dm: CDelegationMap) : bool 
		requires CDelegationMapIsValid(dm)
		ensures var lr := DelegationMapComplete(AbstractifyCDelegationMapToDelegationMap(dm)); var cr := CDelegationMapComplete(dm); (cr) == (lr)
	{
		(forall k :: k in dm)
	}

	function method CDelegationMapHasSameKeys(dm1: CDelegationMap, dm2: CDelegationMap) : bool 
		requires CDelegationMapIsValid(dm1)
		requires CDelegationMapIsValid(dm2)
		ensures var lr := DelegationMapHasSameKeys(AbstractifyCDelegationMapToDelegationMap(dm1), AbstractifyCDelegationMapToDelegationMap(dm2)); var cr := CDelegationMapHasSameKeys(dm1, dm2); (cr) == (lr)
	{
		(forall k :: k in dm1 <==> k in dm2)
	}

	function method CUpdateDelegationMap(dm: CDelegationMap, newkr: KeyRange, host: EndPoint) : CDelegationMap 
		requires CDelegationMapIsValid(dm)
		requires KeyRangeIsValid(newkr)
		requires EndPointIsValid(host)
		ensures CDelegationMapHasSameKeys(dm, CUpdateDelegationMap(dm, newkr, host))
		ensures (forall k :: k in dm ==> CUpdateDelegationMap(dm, newkr, host)[k] == if CKeyRangeContains(newkr, KeyPlus(k)) then host else dm[k])
		ensures var lr := UpdateDelegationMap(AbstractifyCDelegationMapToDelegationMap(dm), AbstractifyKeyRangeToKeyRange(newkr), AbstractifyEndPointToNodeIdentity(host)); var cr := CUpdateDelegationMap(dm, newkr, host); CDelegationMapIsValid(cr) && (AbstractifyCDelegationMapToDelegationMap(cr)) == (lr)
	{
		(map k | k in dm :: if CKeyRangeContains(newkr, KeyPlus(k)) then host else dm[k])
	}

	function method CDelegateForKeyRangeIsHost(dm: CDelegationMap, kr: KeyRange, id: EndPoint) : bool 
		requires CDelegationMapIsValid(dm)
		requires KeyRangeIsValid(kr)
		requires EndPointIsValid(id)
		ensures var lr := DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(dm), AbstractifyKeyRangeToKeyRange(kr), AbstractifyEndPointToNodeIdentity(id)); var cr := CDelegateForKeyRangeIsHost(dm, kr, id); (cr) == (lr)
	{
		(forall k :: k in dm && CKeyRangeContains(kr, KeyPlus(k)) ==> dm[k] == id)
	}

	function method CDelegationMapsAreEqualUpToKey(adm: CDelegationMap, bdm: CDelegationMap, khi: KeyPlus) : bool 
		requires CDelegationMapIsValid(adm)
		requires CDelegationMapIsValid(bdm)
		requires KeyPlusIsValid(khi)
		requires CDelegationMapHasSameKeys(adm, bdm)
		ensures var lr := DelegationMapsAreEqualUpToKey(AbstractifyCDelegationMapToDelegationMap(adm), AbstractifyCDelegationMapToDelegationMap(bdm), AbstractifyKeyPlusToKeyPlus(khi)); var cr := CDelegationMapsAreEqualUpToKey(adm, bdm, khi); (cr) == (lr)
	{
		(forall k :: k in adm && KeyPlusLt(KeyPlus(k), khi) ==> adm[k] == bdm[k])
	}

	function method CDelegateForKey(dm: CDelegationMap, k: Key) : EndPoint 
		requires CDelegationMapIsValid(dm)
		requires KeyIsValid(k)
		requires k in dm
		ensures var lr := DelegateForKey(AbstractifyCDelegationMapToDelegationMap(dm), AbstractifyKeyToKey(k)); var cr := CDelegateForKey(dm, k); EndPointIsValid(cr) && (AbstractifyEndPointToNodeIdentity(cr)) == (lr)
	{
		dm[k]
	}

	function method CBulkUpdateDomain(h: Hashtable, kr: KeyRange, u: Hashtable) : set<Key> 
		requires HashtableIsValid(h)
		requires KeyRangeIsValid(kr)
		requires HashtableIsValid(u)
		ensures var lr := BulkUpdateDomain(AbstractifyHashtableToHashtable(h), AbstractifyKeyRangeToKeyRange(kr), AbstractifyHashtableToHashtable(u)); var cr := CBulkUpdateDomain(h, kr, u); (forall i :: i in cr ==> KeyIsValid(i)) && (AbstractifySet(cr, AbstractifyKeyToKey)) == (lr)
	{
		[Printer for ... hasn't been implemented.]
	}

	function method CBulkUpdateHashtable(h: Hashtable, kr: KeyRange, u: Hashtable) : Hashtable 
		requires HashtableIsValid(h)
		requires KeyRangeIsValid(kr)
		requires HashtableIsValid(u)
		ensures var lr := BulkUpdateHashtable(AbstractifyHashtableToHashtable(h), AbstractifyKeyRangeToKeyRange(kr), AbstractifyHashtableToHashtable(u)); var cr := CBulkUpdateHashtable(h, kr, u); HashtableIsValid(cr) && (AbstractifyHashtableToHashtable(cr)) == (lr)
	{
		(map k | k in CBulkUpdateDomain(h, kr, u) :: if k in u then u[k] else h[k])
	}

	function method CBulkRemoveHashtable(h: Hashtable, kr: KeyRange) : Hashtable 
		requires HashtableIsValid(h)
		requires KeyRangeIsValid(kr)
		ensures var lr := BulkRemoveHashtable(AbstractifyHashtableToHashtable(h), AbstractifyKeyRangeToKeyRange(kr)); var cr := CBulkRemoveHashtable(h, kr); HashtableIsValid(cr) && (AbstractifyHashtableToHashtable(cr)) == (lr)
	{
		(map k | k in h && !CKeyRangeContains(kr, KeyPlus(k)) :: h[k])
	}

	function method CExtractRange(h: Hashtable, kr: KeyRange) : Hashtable 
		requires HashtableIsValid(h)
		requires KeyRangeIsValid(kr)
		ensures var lr := ExtractRange(AbstractifyHashtableToHashtable(h), AbstractifyKeyRangeToKeyRange(kr)); var cr := CExtractRange(h, kr); HashtableIsValid(cr) && (AbstractifyHashtableToHashtable(cr)) == (lr)
	{
		(map k | k in h && CKeyRangeContains(kr, KeyPlus(k)) :: h[k])
	}
}
