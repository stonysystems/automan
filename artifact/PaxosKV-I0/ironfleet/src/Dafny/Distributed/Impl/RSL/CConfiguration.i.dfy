include "../../Protocol/RSL/Constants.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "PacketParsing.i.dfy"
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
import opened Common__NetClient_i
import opened Collections__Seqs_i
import opened GenericRefinement_i

/************************** AutoMan Translation ************************/
  datatype CConfiguration = 
	CConfiguration(
		replica_ids: seq<EndPoint>
	)

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

	function AbstractifyCConfigurationToLConfiguration(s: CConfiguration) : LConfiguration 
		requires CConfigurationIsAbstractable(s)
	{
    /* {} is manually added */
		LConfiguration({}, AbstractifySeq(s.replica_ids, AbstractifyEndPointToNodeIdentity))
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
    FindIndexInSeq(c.replica_ids, id)
		// CFindIndexInSeq(c.replica_ids, id)
	}

  predicate ReplicaIndexValid(idx:int, c:CConfiguration)
  {
    && 0 <= idx < |c.replica_ids|
  }
  /************************** AutoMan Translation End ************************/

// datatype CConfiguration = CConfiguration(
//   client_ids:seq<EndPoint>,
//   replica_ids:seq<EndPoint>)

// datatype CConfiguration = CConfiguration(
//   replica_ids:seq<EndPoint>)

// predicate CConfigurationVaild(c:CConfiguration){
//   && 0 < |c.replica_ids| < 0xffff_ffff_ffff_ffff
//   && CPaxosConfigurationIsAbstractable(c)
//   && LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(c)) <= |c.replica_ids|
//   // 0 < |c.replica_ids| < 100
// }

// function PaxosEndPointIsValid(endPoint:EndPoint, config:CConfiguration) : bool
//   requires CConfigurationVaild(config)
// {
//   EndPointIsValidPublicKey(endPoint)
// }


// predicate CPaxosConfigurationIsAbstractable(config:CConfiguration)
// {
//   && (forall e :: e in config.replica_ids ==> EndPointIsValidPublicKey(e))
//   && SeqIsUnique(config.replica_ids)
// }


// function AbstractifyCPaxosConfigurationToConfiguration(config:CConfiguration) : LConfiguration
//   requires CPaxosConfigurationIsAbstractable(config)
// {
//   LConfiguration({}, AbstractifyEndPointsToNodeIdentities(config.replica_ids))
// }

// lemma lemma_WFCPaxosConfiguration(config:CConfiguration)
//   ensures && CPaxosConfigurationIsAbstractable(config)
//           && 0 < |config.replica_ids|
//           ==> && CPaxosConfigurationIsAbstractable(config)
//               && WellFormedLConfiguration(AbstractifyCPaxosConfigurationToConfiguration(config));
// {
//   if CPaxosConfigurationIsAbstractable(config) && 0 < |config.replica_ids|
//   {
//     //lemma_CardinalityNonEmpty(config.replica_ids);
//     var e := config.replica_ids[0];
//     assert AbstractifyEndPointToNodeIdentity(e) in AbstractifyCPaxosConfigurationToConfiguration(config).replica_ids;
//     assert 0 < |AbstractifyCPaxosConfigurationToConfiguration(config).replica_ids|;
//     var r_replicaIds := AbstractifyCPaxosConfigurationToConfiguration(config).replica_ids;
//     forall i, j | 0 <= i < |r_replicaIds| && 0 <= j < |r_replicaIds|
//       ensures r_replicaIds[i] == r_replicaIds[j] ==> i == j
//     {
//       if r_replicaIds[i] == r_replicaIds[j] {
//         if i != j {
//           assert r_replicaIds[i] == AbstractifyEndPointToNodeIdentity(config.replica_ids[i]);
//           assert r_replicaIds[j] == AbstractifyEndPointToNodeIdentity(config.replica_ids[j]);
//           lemma_AbstractifyEndPointToNodeIdentity_injective(config.replica_ids[i], config.replica_ids[j]);
//           assert config.replica_ids[i] == config.replica_ids[j];
//           reveal_SeqIsUnique();
//           assert i == j;
//           assert false;
//         }
//       }
//     }
//   }
// }

// predicate WFCPaxosConfiguration(config:CConfiguration)
//   ensures WFCPaxosConfiguration(config) ==>
//             && CPaxosConfigurationIsAbstractable(config)
//             && WellFormedLConfiguration(AbstractifyCPaxosConfigurationToConfiguration(config))
// {
//   lemma_WFCPaxosConfiguration(config);
//   && CPaxosConfigurationIsAbstractable(config)
//   && 0 < |config.replica_ids|
// }

// function method CMinQuorumSize(c:CConfiguration) : uint64 
// requires CConfigurationVaild(c)
// {
//   (|c.replica_ids| as uint64)/2+1
// }

// method CReplicaDistinct(replica_ids:seq<EndPoint>, i:uint64, j:uint64) returns (b:bool)
// requires 0 < |replica_ids| < 100
// // requires 0 < |replica_ids| < 0xffff_ffff_ffff_ffff
// {
//   // if 0 <= i < |replica_ids| as uint64 && 0 <= j < |replica_ids| as uint64 && replica_ids[i] == replica_ids[j] {
//   //   b := (i==j);
//   // } else {
//   //   b := false;
//   // }
//   b:= 0 <= i < |replica_ids| as uint64 && 0 <= j < |replica_ids| as uint64 && replica_ids[i] == replica_ids[j] ==> i==j;
//   // b:= 0 <= i as int < |replica_ids| && 0 <= j as int < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i==j;
// }

// predicate ReplicaIndexValid(index:uint64, config:CConfiguration)
// {
//   0 <= index as int < |config.replica_ids|
// }

// // method WFCPaxosConfiguration(c:CConfiguration) returns (b:bool)
// // {
// //   b := 0 < |c.replica_ids| &&  (forall i, j :: ReplicasDistinct(c.replica_ids, i, j));
// //   // b := ture;
// //   // if |c.replica_ids| <= 0{
// //   //   b:= false;
// //   // } else {
// //   //   forall i, j | 0 <= i < |r_replicaIds|as uint64 && 0 <= j < |r_replicaIds| as uint64{
// //   //     if(!CReplicaDistinct(c.replica_ids, i, j)){
// //   //       b := false;
// //   //       break;
// //   //     }
// //   //   }
// //   // }
// // }

// method IsReplicaIndex(idx:uint64, id:EndPoint, c:CConfiguration) returns (b:bool)
// requires CConfigurationVaild(c)
// {
//   b := 0 <= idx < |c.replica_ids| as uint64 && c.replica_ids[idx] == id; 
// }

// // function FindIndexInSeq<T>(s:seq<T>, v:T):uint64
// // {
// //   if v in s then
// //     var idx :| ItemAtPositionInSeq(s, v, idx);
// //     idx
// //   else
// //     -1
// // }

// method CGetReplicaIndex(id:EndPoint, c:CConfiguration) returns (index : uint64)
// requires CConfigurationVaild(c)
// requires id in c.replica_ids
// ensures  ReplicaIndexValid(index, c) && c.replica_ids[index] == id
// ensures  GetReplicaIndex(AbstractifyEndPointToNodeIdentity(id), AbstractifyCPaxosConfigurationToConfiguration(c)) == index as int
// {
//   // FindIndexInSeq(c.replica_ids, id) as uint64
//   var i:uint64 := 0;
  
//   while i as int < |c.replica_ids|
//     invariant i < |c.replica_ids| as uint64
//     invariant forall j :: 0 <= j < i ==> c.replica_ids[j] != id
//   {
//     if id == c.replica_ids[i] {
//       index := i;
      
//       ghost var r_replica := AbstractifyEndPointToNodeIdentity(id);
//       ghost var r_replicas := AbstractifyCPaxosConfigurationToConfiguration(c).replica_ids;
//       assert r_replica == r_replicas[index];
//       assert ItemAtPositionInSeq(r_replicas, r_replica, index as int);
//       calc ==> {
//         true;
//           { reveal_SeqIsUnique(); }
//         forall j :: 0 <= j < |c.replica_ids| && j != i as int ==> c.replica_ids[j] != id;
//       }

//       if exists j :: 0 <= j < |r_replicas| && j != index as int && ItemAtPositionInSeq(r_replicas, r_replica, j) {
//         ghost var j :| 0 <= j < |r_replicas| && j != index as int && ItemAtPositionInSeq(r_replicas, r_replica, j);
//         assert r_replicas[j] == r_replica;
//         assert AbstractifyEndPointToNodeIdentity(c.replica_ids[j]) == r_replica;
//         lemma_AbstractifyEndPointToNodeIdentity_injective(c.replica_ids[i], c.replica_ids[j]);
//         assert false;
//       }
//       assert forall j :: 0 <= j < |r_replicas| && j != index as int ==> !ItemAtPositionInSeq(r_replicas, r_replica, j);
//       assert FindIndexInSeq(r_replicas, r_replica) == index as int;
//       return;
//     }

//     if i == (|c.replica_ids| as uint64) - 1 {
//       return;
//     }

//     i := i + 1;
//   }
// }

} 
