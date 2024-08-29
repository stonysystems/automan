include ""


module Impl_LiveRSL__Configuration_i 
{

	datatype CConfiguration = 
	CConfiguration(
		replica_ids: seq<CNodeIdentity>
	)

	predicate CConfigurationIsValid(s: CConfiguration) 
	{
		CConfigurationIsAbstractable(s) 
		&& 
		(forall i :: i in s.replica_ids ==> CNodeIdentityIsValid(i))
	}

	predicate CConfigurationIsAbstractable(s: CConfiguration) 
	{
		(forall i :: i in s.replica_ids ==> CNodeIdentityIsAbstractable(i))
	}

	function AbstractifyCConfigurationToLConfiguration(s: CConfiguration) : LConfiguration 
		requires CConfigurationIsAbstractable(s)
	{
		LConfiguration(AbstractifySeq(s.replica_ids, AbstractifyCNodeIdentityToNodeIdentity))
	}

	function method CMinQuorumSize(c: CConfiguration) : Cint 
		requires CConfigurationIsValid(c)
		ensures CMinQuorumSize(c) == LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(c))
	{
		|c.replica_ids| / 2 + 1
	}

	function method CReplicasDistinct(replica_ids: seq<CNodeIdentity>, i: Cint, j: Cint) : Cbool 
		requires (forall i :: i in replica_ids ==> CNodeIdentityIsValid(i))
		requires CintIsValid(i)
		requires CintIsValid(j)
		ensures CReplicasDistinct(replica_ids, i, j) == ReplicasDistinct(AbstractifySeq(replica_ids, AbstractifyCNodeIdentityToNodeIdentity), i, j)
	{
		HOLDER
	}

	function method CWellFormedLConfiguration(c: CConfiguration) : Cbool 
		requires CConfigurationIsValid(c)
		ensures CWellFormedLConfiguration(c) == WellFormedLConfiguration(AbstractifyCConfigurationToLConfiguration(c))
	{
		HOLDER
	}

	function method CIsReplicaIndex(idx: Cint, id: CNodeIdentity, c: CConfiguration) : Cbool 
		requires CintIsValid(idx)
		requires CNodeIdentityIsValid(id)
		requires CConfigurationIsValid(c)
		ensures CIsReplicaIndex(idx, id, c) == IsReplicaIndex(idx, AbstractifyCNodeIdentityToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c))
	{
		HOLDER
	}

	function method CGetReplicaIndex(id: CNodeIdentity, c: CConfiguration) : Cint 
		requires CNodeIdentityIsValid(id)
		requires CConfigurationIsValid(c)
		requires id in c.replica_ids
		ensures var idx := CGetReplicaIndex(id, c); 0 <= idx && idx < |c.replica_ids| && c.replica_ids[idx] == id
		ensures CGetReplicaIndex(id, c) == GetReplicaIndex(AbstractifyCNodeIdentityToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c))
	{
		CFindIndexInSeq(c.replica_ids, id)
	}
}
