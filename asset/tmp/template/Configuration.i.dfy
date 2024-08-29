include "Types.i.dfy"
include "ToBeFilled.i.dfy"
include "ToBeFilled.i.dfy"

module Impl_LiveRSL__Configuration_i {
 	import opened Impl_LiveRSL__Types_i
	import opened ToBeFilled
	import opened ToBeFilled
	import opened ToBeFilled

	datatype CConfiguration = 
	CConfiguration
	(
		replica_ids : seq<EndPoint>
	)

	predicate CConfigurationIsValid(
		s : CConfiguration)
		
	{
		CConfigurationIsAbstractable(s)
		&&
		(forall i :: i in s.replica_ids ==> i.EndPoint? && EndPointIsValid(i))
	}

	predicate CConfigurationIsAbstractable(
		s : CConfiguration)
		
	{
		(forall i :: i in s.replica_ids ==> i.EndPoint? && EndPointIsAbstractable(i))
	}

	function AbstractifyCConfigurationToLConfiguration(
		s : CConfiguration) : LConfiguration
		requires CConfigurationIsAbstractable(s)
	{
		LConfiguration(AbstractifySeq(s.replica_ids, AbstractifyEndPointToNodeIdentity))
	}

	function method CMinQuorumSize(
		c : CConfiguration) : int
		requires CConfigurationIsValid(c)
		ensures var r' := CMinQuorumSize(c); var r := LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(c)); (r) == (r')
	{
		|c.replica_ids| / 2 + 1
	}

	function method CReplicasDistinct(
		replica_ids : seq<EndPoint> ,
		i : int ,
		j : int) : bool
		requires (forall i :: i in replica_ids ==> i.EndPoint? && EndPointIsValid(i))
		ensures var bc := CReplicasDistinct(replica_ids, i, j); var bl := ReplicasDistinct(AbstractifySeq(replica_ids, AbstractifyEndPointToNodeIdentity), i, j); (bl) == (bc)
	{
		0 <= i < |replica_ids| && 0 <= j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j
	}

	function method CWellFormedLConfiguration(
		c : CConfiguration) : bool
		requires CConfigurationIsValid(c)
		ensures var bc := CWellFormedLConfiguration(c); var bl := WellFormedLConfiguration(AbstractifyCConfigurationToLConfiguration(c)); (bl) == (bc)
	{

		&&
		0 < |c.replica_ids|
		&&
		(forall i, j :: CReplicasDistinct(c.replica_ids, i, j))
	}

	function method CIsReplicaIndex(
		idx : int ,
		id : EndPoint ,
		c : CConfiguration) : bool
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		ensures var bc := CIsReplicaIndex(idx, id, c); var bl := IsReplicaIndex(idx, AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c)); (bl) == (bc)
	{

		&&
		0 <= idx < |c.replica_ids|
		&&
		c.replica_ids[idx] == id
	}

	function method CGetReplicaIndex(
		id : EndPoint ,
		c : CConfiguration) : int
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		requires id in c.replica_ids
		ensures var r' := CGetReplicaIndex(id, c); var r := GetReplicaIndex(AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c)); (r) == (r')
		ensures var idx := CGetReplicaIndex(id, c); 0 <= idx < |c.replica_ids| && c.replica_ids[idx] == id
	{
		FindIndexInSeq(c.replica_ids, id)
	}
 
}
