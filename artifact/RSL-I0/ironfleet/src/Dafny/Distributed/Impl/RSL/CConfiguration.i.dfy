include "../../Protocol/RSL/Constants.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../LiveRSL/PacketParsing.i.dfy"
include "CParameters.i.dfy"

module LiveRSL__CPaxosConfiguration_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveRSL__Constants_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__PacketParsing_i
  import opened LiveRSL__ParametersState_i
  import opened Common__NodeIdentity_i
  import opened Common__SeqIsUniqueDef_i
  import opened Common__UdpClient_i
  import opened Collections__Seqs_i
  import opened GenericRefinement_i

  /************************** AutoMan Translation ************************/
  /** 4 + 0 */
  datatype CConfiguration = 
	CConfiguration(
		replica_ids: seq<EndPoint>
	)

  /** 0 + 15 */
	predicate CConfigurationIsValid(s: CConfiguration) 
	{
		CConfigurationIsAbstractable(s) 
		&& 
		(forall i :: i in s.replica_ids ==> EndPointIsValid(i))
    /* Below is manually added */
    &&
      SeqIsValid(s.replica_ids, EndPointIsValid)
    &&
      0 < |s.replica_ids| < 0xffff_ffff_ffff_ffff
    &&
      (forall i, j :: CReplicasDistinct(s.replica_ids,i,j))
    &&
      (forall i,j :: 0 <= i < |s.replica_ids| && 0 <= j < |s.replica_ids| && s.replica_ids[i] == s.replica_ids[j] ==> i == j)
    &&
      LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(s)) <= |s.replica_ids|
	}

  /** 0 + 10 */
	predicate CConfigurationIsAbstractable(s: CConfiguration) 
	{
		(forall i :: i in s.replica_ids ==> 
      /* manually added */
      i.EndPoint? &&
    EndPointIsAbstractable(i))
    /* Below is manually added */
    &&
      SeqIsUnique(s.replica_ids)
	}

  /** 0 + 5 + 1 */
	function AbstractifyCConfigurationToLConfiguration(s: CConfiguration) : LConfiguration 
		requires CConfigurationIsAbstractable(s)
	{
		LConfiguration({}, AbstractifySeq(s.replica_ids, AbstractifyEndPointToNodeIdentity))
	}

  /** 4 + 2 */
  function method CMinQuorumSize(c: CConfiguration) : int 
		requires CConfigurationIsValid(c)
		ensures CMinQuorumSize(c) == LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(c))
	{
		|c.replica_ids| / 2 + 1
	}

  /** 4 + 2 */
	function method CReplicasDistinct(replica_ids: seq<EndPoint>, i: int, j: int) : bool 
		requires (forall i :: i in replica_ids ==> EndPointIsValid(i))
		ensures CReplicasDistinct(replica_ids, i, j) == ReplicasDistinct(AbstractifySeq(replica_ids, AbstractifyEndPointToNodeIdentity), i, j)
	{
		0 <= i && i < |replica_ids| && 0 <= j && j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j
	}

  /** 6 + 3 */
	function method CIsReplicaIndex(idx: int, id: EndPoint, c: CConfiguration) : bool 
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		ensures CIsReplicaIndex(idx, id, c) == IsReplicaIndex(idx, AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c))
	{
		0 <= idx && idx < |c.replica_ids| 
		&& 
		c.replica_ids[idx] == id
	}

  /** 4 + 5 */
  function method CGetReplicaIndex(id: EndPoint, c: CConfiguration) : int 
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		requires id in c.replica_ids
		ensures var idx := CGetReplicaIndex(id, c); 0 <= idx && idx < |c.replica_ids| && c.replica_ids[idx] == id
		ensures CGetReplicaIndex(id, c) == GetReplicaIndex(AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c))
	{
    FindIndexInSeq(c.replica_ids, id)
	}

  /************************** AutoMan Translation End ************************/

  predicate ReplicaIndexValid(idx:int, c:CConfiguration)
  {
    && 0 <= idx < |c.replica_ids|
  }

}
