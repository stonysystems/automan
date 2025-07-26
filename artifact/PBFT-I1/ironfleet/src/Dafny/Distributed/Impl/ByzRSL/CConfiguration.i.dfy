include "../../Protocol/ByzRSL/Constants.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../LiveByzRSL/PacketParsing.i.dfy"
include "CParameters.i.dfy"

module LiveByzRSL__CConfiguration_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__Constants_i
  import opened LiveByzRSL__Configuration_i
//   import opened LiveRSL__PacketParsing_i
  import opened LiveByzRSL__ParametersState_i
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
		ensures var lr := LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(c)); var cr := CMinQuorumSize(c); (cr) == (lr)
	{
		|c.replica_ids| / 2 + 1
	}

  /** 4 + 2 */
  function method CByzQuorumSize(c: CConfiguration) : int 
		requires CConfigurationIsValid(c)
		ensures var lr := LByzQuorumSize(AbstractifyCConfigurationToLConfiguration(c)); var cr := CByzQuorumSize(c); (cr) == (lr)
	{
		2 * |c.replica_ids| / 3 + 1
	}

  /** 4 + 2 */
	function method CReplicasDistinct(replica_ids: seq<EndPoint>, i: int, j: int) : bool 
		requires (forall i :: i in replica_ids ==> EndPointIsValid(i))
		ensures CReplicasDistinct(replica_ids, i, j) == ReplicasDistinct(AbstractifySeq(replica_ids, AbstractifyEndPointToNodeIdentity), i, j)
	{
		0 <= i && i < |replica_ids| && 0 <= j && j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j
	}

  /** 4 + 2 */
  function method CReplicasIsUnique(replica_ids: seq<EndPoint>) : bool 
		requires (forall i :: i in replica_ids ==> EndPointIsValid(i))
		ensures var lr := ReplicasIsUnique(AbstractifySeq(replica_ids, AbstractifyEndPointToNodeIdentity)); var cr := CReplicasIsUnique(replica_ids); (cr) == (lr)
	{
		(forall i, j :: 0 <= i && i < |replica_ids| && 0 <= j && j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j)
	}

  /** 6 + 3 */
	function method CIsReplicaIndex(idx: int, id: EndPoint, c: CConfiguration) : bool 
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		ensures var lr := IsReplicaIndex(idx, AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c)); var cr := CIsReplicaIndex(idx, id, c); (cr) == (lr)
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
		ensures var idx := CGetReplicaIndex(id, c); CIsReplicaIndex(idx, id, c)
		ensures var lr := GetReplicaIndex(AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c)); var cr := CGetReplicaIndex(id, c); (cr) == (lr)
	{
		FindIndexInSeq(c.replica_ids, id)
	}

  /************************** AutoMan Translation End ************************/

  predicate ReplicaIndexValid(idx:int, c:CConfiguration)
  {
    && 0 <= idx < |c.replica_ids|
  }

}
