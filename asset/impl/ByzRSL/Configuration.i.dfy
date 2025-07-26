/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__Configuration_i
**********************************************************************/

include ""


module Impl_LiveByzRSL__Configuration_i 
{

	datatype CConfiguration = 
	CConfiguration(
		clientIds: set<EndPoint>, 
		replica_ids: seq<EndPoint>
	)

	predicate CConfigurationIsValid(s: CConfiguration) 
	{
		CConfigurationIsAbstractable(s) 
		&& 
		(forall i :: i in s.clientIds ==> EndPointIsValid(i)) 
		&& 
		(forall i :: i in s.replica_ids ==> EndPointIsValid(i))
	}

	predicate CConfigurationIsAbstractable(s: CConfiguration) 
	{
		(forall i :: i in s.clientIds ==> EndPointIsAbstractable(i)) 
		&& 
		(forall i :: i in s.replica_ids ==> EndPointIsAbstractable(i))
	}

	function AbstractifyCConfigurationToLConfiguration(s: CConfiguration) : LConfiguration 
		requires CConfigurationIsAbstractable(s)
	{
		LConfiguration(AbstractifySet(s.clientIds, AbstractifyEndPointToNodeIdentity), AbstractifySeq(s.replica_ids, AbstractifyEndPointToNodeIdentity))
	}

	function method CMinQuorumSize(c: CConfiguration) : int 
		requires CConfigurationIsValid(c)
		ensures var lr := LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(c)); var cr := CMinQuorumSize(c); (cr) == (lr)
	{
		|c.replica_ids| / 2 + 1
	}

	function method CByzQuorumSize(c: CConfiguration) : int 
		requires CConfigurationIsValid(c)
		ensures var lr := LByzQuorumSize(AbstractifyCConfigurationToLConfiguration(c)); var cr := CByzQuorumSize(c); (cr) == (lr)
	{
		2 * |c.replica_ids| / 3 + 1
	}

	function method CReplicasDistinct(replica_ids: seq<EndPoint>, i: int, j: int) : bool 
		requires (forall i :: i in replica_ids ==> EndPointIsValid(i))
		ensures var lr := ReplicasDistinct(AbstractifySeq(replica_ids, AbstractifyEndPointToNodeIdentity), i, j); var cr := CReplicasDistinct(replica_ids, i, j); (cr) == (lr)
	{
		0 <= i && i < |replica_ids| && 0 <= j && j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j
	}

	function method CReplicasIsUnique(replica_ids: seq<EndPoint>) : bool 
		requires (forall i :: i in replica_ids ==> EndPointIsValid(i))
		ensures var lr := ReplicasIsUnique(AbstractifySeq(replica_ids, AbstractifyEndPointToNodeIdentity)); var cr := CReplicasIsUnique(replica_ids); (cr) == (lr)
	{
		(forall i, j :: 0 <= i && i < |replica_ids| && 0 <= j && j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j)
	}

	function method CWellFormedLConfiguration(c: CConfiguration) : bool 
		requires CConfigurationIsValid(c)
		ensures var lr := WellFormedLConfiguration(AbstractifyCConfigurationToLConfiguration(c)); var cr := CWellFormedLConfiguration(c); (cr) == (lr)
	{
		0 < |c.replica_ids| 
		&& 
		(forall i, j :: CReplicasDistinct(c.replica_ids, i, j)) 
		&& 
		CReplicasIsUnique(c.replica_ids)
	}

	function method CIsReplicaIndex(idx: int, id: EndPoint, c: CConfiguration) : bool 
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		ensures var lr := IsReplicaIndex(idx, AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c)); var cr := CIsReplicaIndex(idx, id, c); (cr) == (lr)
	{
		0 <= idx && idx < |c.replica_ids| 
		&& 
		c.replica_ids[idx] == id
	}

	function method CGetReplicaIndex(id: EndPoint, c: CConfiguration) : int 
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		requires id in c.replica_ids
		ensures var idx := CGetReplicaIndex(id, c); CIsReplicaIndex(idx, id, c)
		ensures var lr := GetReplicaIndex(AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c)); var cr := CGetReplicaIndex(id, c); (cr) == (lr)
	{
		CFindIndexInSeq(c.replica_ids, id)
	}
}
