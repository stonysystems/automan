include ""


module Impl_LiveRSL__Configuration_i 
{

	datatype CConfiguration = 
	CConfiguration(
		replica_ids: seq<EndPoint>
	)

	predicate CConfigurationIsValid(s: CConfiguration) 
	{
		CConfigurationIsAbstractable(s) 
		&& 
		(forall i :: i in s.replica_ids ==> EndPointIsValid(i))
	}

	predicate CConfigurationIsAbstractable(s: CConfiguration) 
	{
		(forall i :: i in s.replica_ids ==> EndPointIsAbstractable(i))
	}

	function AbstractifyCConfigurationToLConfiguration(s: CConfiguration) : LConfiguration 
		requires CConfigurationIsAbstractable(s)
	{
		LConfiguration(AbstractifySeq(s.replica_ids, AbstractifyEndPointToNodeIdentity))
	}

	function method CMinQuorumSize(c: CConfiguration) : int 
		requires CConfigurationIsValid(c)
		ensures CMinQuorumSize(c) == LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(c))
	{
		|c.replica_ids| / 2 + 1
	}

	function method CReplicasDistinct(replica_ids: seq<EndPoint>, i: int, j: int) : bool 
		requires (forall i :: i in replica_ids ==> EndPointIsValid(i))
		ensures CReplicasDistinct(replica_ids, i, j) == ReplicasDistinct(AbstractifySeq(replica_ids, AbstractifyEndPointToNodeIdentity), i, j)
	{
		0 <= i && i < |replica_ids| && 0 <= j && j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j
	}

	function method CWellFormedLConfiguration(c: CConfiguration) : bool 
		requires CConfigurationIsValid(c)
		ensures CWellFormedLConfiguration(c) == WellFormedLConfiguration(AbstractifyCConfigurationToLConfiguration(c))
	{
		0 < |c.replica_ids| 
		&& 
		(forall i, j :: CReplicasDistinct(c.replica_ids, i, j))
	}

	function method CIsReplicaIndex(idx: int, id: EndPoint, c: CConfiguration) : bool 
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		ensures CIsReplicaIndex(idx, id, c) == IsReplicaIndex(idx, AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c))
	{
		0 <= idx && idx < |c.replica_ids| 
		&& 
		c.replica_ids[idx] == id
	}

	function method CGetReplicaIndex(id: EndPoint, c: CConfiguration) : int 
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		requires id in c.replica_ids
		ensures var idx := CGetReplicaIndex(id, c); 0 <= idx && idx < |c.replica_ids| && c.replica_ids[idx] == id
		ensures CGetReplicaIndex(id, c) == GetReplicaIndex(AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c))
	{
		CFindIndexInSeq(c.replica_ids, id)
	}
}
