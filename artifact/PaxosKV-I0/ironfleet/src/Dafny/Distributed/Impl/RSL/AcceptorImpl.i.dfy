include "../../Protocol/RSL/Acceptor.i.dfy"
include "Broadcast.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"

module LiveRSL__AcceptorModel_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__Acceptor_i
// import opened LiveRSL__AcceptorState_i
// import opened LiveRSL__CLastCheckpointedMap_i
import opened LiveRSL__CMessage_i
// import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Message_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ParametersState_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__Types_i
import opened Impl__LiveRSL__Broadcast_i
import opened Collections__Maps_i
import opened Collections__Maps2_s
import opened Collections__Sets_i
import opened Common__NodeIdentity_i
import opened Common__UpperBound_s
import opened Common__UpperBound_i
import opened Common__Util_i
import opened Environment_s
import opened Collections__CountMatches_i
import opened GenericRefinement_i


  /************************** AutoMan Translation ************************/

  datatype CAcceptor = 
	CAcceptor(
		constants: CReplicaConstants, 
		max_bal: CBallot, 
		votes: CVotes, 
		last_checkpointed_operation: seq<COperationNumber>, 
		log_truncation_point: COperationNumber
	)

	predicate CAcceptorIsValid(s: CAcceptor) 
	{
		CAcceptorIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CBallotIsValid(s.max_bal) 
		&& 
		CVotesIsValid(s.votes) 
		&& 
		(forall i :: i in s.last_checkpointed_operation ==> COperationNumberIsValid(i)) 
		&& 
		COperationNumberIsValid(s.log_truncation_point)
    && /* Manually added */
    |s.last_checkpointed_operation| == |s.constants.all.config.replica_ids|
	}

	predicate CAcceptorIsAbstractable(s: CAcceptor) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CBallotIsAbstractable(s.max_bal) 
		&& 
		CVotesIsAbstractable(s.votes) 
		&& 
		(forall i :: i in s.last_checkpointed_operation ==> COperationNumberIsAbstractable(i)) 
		&& 
		COperationNumberIsAbstractable(s.log_truncation_point)
	}

  function AbstractifyCAcceptorToLAcceptor(s: CAcceptor) : LAcceptor 
		requires CAcceptorIsAbstractable(s)
	{
		LAcceptor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_bal), AbstractifyCVotesToVotes(s.votes), AbstractifySeq(s.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCOperationNumberToOperationNumber(s.log_truncation_point))
	}

  function method CIsLogTruncationPointValid(log_truncation_point: COperationNumber, last_checkpointed_operation: seq<COperationNumber>, config: CConfiguration) : bool 
		requires COperationNumberIsValid(log_truncation_point)
		requires (forall i :: i in last_checkpointed_operation ==> COperationNumberIsValid(i))
		requires CConfigurationIsValid(config)
		ensures CIsLogTruncationPointValid(log_truncation_point, last_checkpointed_operation, config) == IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCConfigurationToLConfiguration(config))
	{
    /* manually add */
    assert AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber) == last_checkpointed_operation;
		IsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, CMinQuorumSize(config))
	}

  function method CRemoveVotesBeforeLogTruncationPoint(votes: CVotes, log_truncation_point: COperationNumber) : CVotes 
		requires CVotesIsValid(votes)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var votes' := CRemoveVotesBeforeLogTruncationPoint(votes, log_truncation_point); CVotesIsValid(votes') && RemoveVotesBeforeLogTruncationPoint(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	{
    var t1 := (map opn | opn in votes && opn >= log_truncation_point :: votes[opn]); 	
		// var t1 := (forall opn | opn in votes && opn >= log_truncation_point :: votes[opn]); 

    lemma_voteLen(t1);	
		t1
	}

	function method CAddVoteAndRemoveOldOnes(votes: CVotes, new_opn: COperationNumber, new_vote: CVote, log_truncation_point: COperationNumber) : CVotes 
		requires CVotesIsValid(votes)
		requires COperationNumberIsValid(new_opn)
		requires CVoteIsValid(new_vote)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var votes' := CAddVoteAndRemoveOldOnes(votes, new_opn, new_vote, log_truncation_point); CVotesIsValid(votes') && LAddVoteAndRemoveOldOnes(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(new_opn), AbstractifyCVoteToVote(new_vote), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	{
		var t1 := (map opn | opn in votes.Keys + {new_opn} && opn >= log_truncation_point :: if opn == new_opn then new_vote else votes[opn]); 		
    lemma_voteLen(t1);
		t1
	}

  function method CAcceptorInit(c: CReplicaConstants) : CAcceptor 
		requires CReplicaConstantsIsValid(c)
		ensures var a := CAcceptorInit(c); CAcceptorIsValid(a) && LAcceptorInit(AbstractifyCAcceptorToLAcceptor(a), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := c; 		
		var t2 := CBallot(0, 0); 		
		var t3 := map[]; 		
		var t4 := seq(|c.all.config.replica_ids|, (idx) => 0); 		
		var t5 := 0; 		
		CAcceptor(t1, t2, t3, t4, t5)
	}

  function method CAcceptorProcess1a(s: CAcceptor, inp: CPacket) : (CAcceptor, OutboundPackets) 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_1a?
		ensures var (s', broadcast_sent_packets) := CAcceptorProcess1a(s, inp); CAcceptorIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LAcceptorProcess1a(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := var m := inp.msg; 
      var t1 := 
        if inp.src in s.constants.all.config.replica_ids && CBalLt(s.max_bal, m.bal_1a) /*&& CReplicaConstantsValid(s.constants)*/ then 
          var t1 := 
            PacketSequence(
            [CPacket(inp.src, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_1b(m.bal_1a, s.log_truncation_point, s.votes))]
            ); 
          var t2 := s.(max_bal := m.bal_1a); 
          (t2, t1) 
        else 
          var t1 := s; 
          var t2 := PacketSequence([]); 
          (t1, t2); 
        (t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CAcceptorProcess2a(s: CAcceptor, inp: CPacket) : (CAcceptor, OutboundPackets) 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_2a?
		requires inp.src in s.constants.all.config.replica_ids
		requires CBalLeq(s.max_bal, inp.msg.bal_2a)
		requires CLeqUpperBound(inp.msg.opn_2a, s.constants.all.params.max_integer_val)
		ensures var (s', broadcast_sent_packets) := CAcceptorProcess2a(s, inp); CAcceptorIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LAcceptorProcess2a(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := var m := inp.msg; 
    var t1 := var newLogTruncationPoint := 
      if inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then 
        inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 
      else 
        s.log_truncation_point; 
    var t1 := Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2b(m.bal_2a, m.opn_2a, m.val_2a))); 
    var t2 := m.bal_2a; 
    var t3 := newLogTruncationPoint; 
    var t4 := 
      if s.log_truncation_point <= inp.msg.opn_2a then 
        var t1 := CAddVoteAndRemoveOldOnes(s.votes, m.opn_2a, CVote(m.bal_2a, m.val_2a), newLogTruncationPoint); 
        t1 
      else 
        var t1 := s.votes; 
        t1; 
      var t5 := s.constants; 
      var t6 := s.last_checkpointed_operation; 
      (CAcceptor(t5, t2, t4, t6, t3), t1); (t1.1, t1.0); 		
		(t1.1, t1.0)
	}

  function method CAcceptorProcessHeartbeat(s: CAcceptor, inp: CPacket) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Heartbeat?
		ensures var s' := CAcceptorProcessHeartbeat(s, inp); CAcceptorIsValid(s') && LAcceptorProcessHeartbeat(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		var t1 := 
      if inp.src in s.constants.all.config.replica_ids then 
        var t1 := 
        var sender_index := CGetReplicaIndex(inp.src, s.constants.all.config); 
        var t1 := 
          if 0 <= sender_index && sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then 
            var t1 := s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt]; 
            var t2 := s.constants; 
            var t3 := s.max_bal; 
            var t4 := s.votes; 
            var t5 := s.log_truncation_point; 
            CAcceptor(t2, t3, t4, t1, t5) 
          else 
            var t1 := s; 
            t1; 
          t1; 
        t1 
      else 
        var t1 := s; 
        t1; 		
		t1
	}

  function method CAcceptorTruncateLog(s: CAcceptor, opn: COperationNumber) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CAcceptorTruncateLog(s, opn); CAcceptorIsValid(s') && LAcceptorTruncateLog(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{ 
    var t := seq(10, (idx) => 1); 
    var t1 := 
      if opn <= s.log_truncation_point then 
        var t1 := s; 
        t1 
      else 
        var t1 := 
        var a := s.log_truncation_point; 
        var t1 := CRemoveVotesBeforeLogTruncationPoint(s.votes, opn); 
        var t2 := s.(log_truncation_point := opn, votes := t1); 
        t2; 
      t1;  		
		t1
	}
	// function method CRemoveVotesBeforeLogTruncationPoint(votes: CVotes, log_truncation_point: COperationNumber) : CVotes 
	// 	requires CVotesIsValid(votes)
	// 	requires COperationNumberIsValid(log_truncation_point)
	// 	ensures var votes' := CRemoveVotesBeforeLogTruncationPoint(votes, log_truncation_point); CVotesIsValid(votes') && RemoveVotesBeforeLogTruncationPoint(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	// {
	// 	CVotes()
	// }

  lemma {:axiom} lemma_voteLen(votes:CVotes)
    ensures |votes| < max_votes_len()
  /************************** AutoMan Translation End ********************/ 

// datatype AcceptorState = AcceptorState(
//   constants:CReplicaConstants,
//   maxBallot:CBallot,
//   votes:CVotes,
//   last_checkpointed_operation:seq<COperationNumber>,
//   log_truncation_point:COperationNumber
//   )
//   // minVotedOpn:COperationNumber

// predicate AcceptorIsValid(acceptor:AcceptorState)
// {
//   && AcceptorIsAbstractable(acceptor)
//   && CReplicaConstansValid(acceptor.constants)
//   && CBallotValid(acceptor.maxBallot)
//   && CVotesValid(acceptor.votes)
//   // && 0 < |acceptor.last_checkpointed_operation| < 0xffff_ffff_ffff_ffff
//   && |acceptor.last_checkpointed_operation| == |acceptor.constants.all.config.replica_ids|
//   // && COperationNumberValid(acceptor.log_truncation_point)
//   && acceptor.constants.all.params.max_integer_val > acceptor.constants.all.params.max_log_length > 0
//   && acceptor.log_truncation_point < 0x8000_0000_0000_0000
//   && (forall opn :: opn in acceptor.votes.v ==>
//               acceptor.log_truncation_point <= opn <=
//                 UpperBoundedAdditionImpl(acceptor.log_truncation_point, acceptor.constants.all.params.max_log_length-1, acceptor.constants.all.params.max_integer_val))
//               //  AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point)
//               //  <= AbstractifyCOperationNumberToOperationNumber(opn)
//               //  <= UpperBoundedAddition(AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point),
//               //                         (acceptor.constants.all.params.max_log_length-1) as int,
//               //                         UpperBoundFinite(acceptor.constants.all.params.max_integer_val as int)))
//   // && UpperBoundedAdditionImpl(acceptor.log_truncation_point, acceptor.constants.all.params.max_log_length-1, acceptor.constants.all.params.max_integer_val)
// }

// predicate AcceptorIsAbstractable(acceptor:AcceptorState)
// {
//   && ReplicaConstantsStateIsAbstractable(acceptor.constants)
//   && CBallotIsAbstractable(acceptor.maxBallot)
//   && CVotesIsAbstractable(acceptor.votes)
// }

// function {:opaque} AbstractifyCLastCheckpointedMapToOperationNumberSequence(s:seq<COperationNumber>) : seq<OperationNumber>
//   ensures |AbstractifyCLastCheckpointedMapToOperationNumberSequence(s)| == |s|
//   ensures forall i :: 0 <= i < |s| ==> AbstractifyCOperationNumberToOperationNumber(s[i]) == AbstractifyCLastCheckpointedMapToOperationNumberSequence(s)[i]
// {
//   if |s| == 0 then []
//   else [AbstractifyCOperationNumberToOperationNumber(s[0])] + AbstractifyCLastCheckpointedMapToOperationNumberSequence(s[1..])
// }

// function AbstractifyAcceptorStateToAcceptor(acceptor:AcceptorState) : LAcceptor
//     requires AcceptorIsAbstractable(acceptor);
// {
//   LAcceptor(
//     AbstractifyReplicaConstantsStateToLReplicaConstants(acceptor.constants),
//     AbstractifyCBallotToBallot(acceptor.maxBallot),
//     AbstractifyCVotesToVotes(acceptor.votes),
//     AbstractifyCLastCheckpointedMapToOperationNumberSequence(acceptor.last_checkpointed_operation),
//     AbstractifyCOperationNumberToOperationNumber(acceptor.log_truncation_point))
// }

// predicate CommonAcceptorPreconditions(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint)
// {
//   && AcceptorIsValid(acceptor)
//   && AcceptorIsAbstractable(acceptor)
//   && CReplicaConstansValid(acceptor.constants)
//   && CMessageIsValid(in_msg)
//   && CMessageIsAbstractable(in_msg)
//   && PaxosEndPointIsValid(sender, acceptor.constants.all.config)
// }

// predicate NextAcceptorState_ProcessHeartbeatPreconditions(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint)
// {
//   && CommonAcceptorPreconditions(acceptor, in_msg, sender)
//   && in_msg.CMessage_Heartbeat?
//   && CPaxosConfigurationIsAbstractable(acceptor.constants.all.config)
// }

// predicate NextAcceptorState_Phase1Preconditions(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint)
// {
//   && CommonAcceptorPreconditions(acceptor, in_msg, sender)
//   && in_msg.CMessage_1a?
// }

// predicate NextAcceptorState_Phase2Preconditions_AlwaysEnabled(acceptor:AcceptorState, in_msg:CMessage, sender:EndPoint)
// {
//   && CommonAcceptorPreconditions(acceptor, in_msg, sender)
//   && in_msg.CMessage_2a?
//   && CPaxosConfigurationIsAbstractable(acceptor.constants.all.config)
// }

// // function method IsNthHighestValueInSequenceUint64(v:uint64, s:seq<uint64>, n:uint64) : bool
// // {
// //   && 0 < n <= |s| as uint64
// //   && v in s
// //   && CountMatchesInSeq(s, x => x > v) as uint64 < n
// //   && CountMatchesInSeq(s, x => x >= v) as uint64 >= n
// // }

// // function method CountMatchesInSeq2<T(!new)>(s:seq<T>, f:T-->bool):uint64
// //   reads f.reads
// // {
// //   if |s| == 0 then
// //     0
// //   else
// //     CountMatchesInSeq2(s[1..], f) + if f(s[0]) then 1 else 0
// // }


// // 这个是把common里的predicate翻译成了method
// method IsNthHighestValueInSequenceUint64(v:uint64, s:seq<uint64>, n:uint64) returns (b:bool)
// {
//   var a := 0  < n as int <= |s|
//   && v in s;
//   var i:int := 0;
//   var count:int := 0;
//   if(a){
//     while i < |s|
//     {
//       if s[i] >= v
//       {
//         count := count + 1;
//       }
//       i := i + 1;
//     }
//   }
//   b := a && count >= n as int;
// }

// // check if the checkpoint on majority larger than truncation point
// method CIsLogTruncationPointValid(log_truncation_point:COperationNumber, last_checkpointed_operation:seq<COperationNumber>,
//                                     config:CConfiguration) returns (b:bool)
// requires CConfigurationVaild(config)
// {
//   // var quorum := CMinQuorumSize(config);
//   b := IsNthHighestValueInSequenceUint64(log_truncation_point,
//                               last_checkpointed_operation,
//                               CMinQuorumSize(config));
// }

// // 对应 protocol 里 RemoveVotesBeforeLogTruncationPoint
// // 是不是可以直接按原始的翻译，带forall量词？
// // 这个翻译算是理解逻辑后自己写的
// method CRemoveVotesBeforeLogTruncationPoint(votes:CVotes, newLogTruncationPoint:COperationNumber) returns (votes':CVotes)
// {
//   var new_votes := (map op | op in votes.v && op >= newLogTruncationPoint :: votes.v[op]);
//   votes' := CVotes(new_votes);
// }

// // 对应 protocol 里 LAddVoteAndRemoveOldOnes
// // 同上
// method CAddVoteAndRemoveOldOnes(votes:CVotes, new_vote:CVote, new_opn:COperationNumber, newLogTruncationPoint:COperationNumber) returns (votes':CVotes)
// {
//   var updated_votes := votes.v[new_opn := new_vote];
//   var new_votes := (map op | op in updated_votes && op >= newLogTruncationPoint :: updated_votes[op]);
//   votes' := CVotes(new_votes);
// }

// predicate NextAcceptorState_InitPostconditions(acceptor:AcceptorState, rcs:CReplicaConstants)
//   requires CReplicaConstansValid(rcs)
// {
//   && AcceptorIsValid(acceptor)
//   && AcceptorIsAbstractable(acceptor)
//   && acceptor.constants == rcs
//   && LAcceptorInit(AbstractifyAcceptorStateToAcceptor(acceptor), AbstractifyReplicaConstantsStateToLReplicaConstants(rcs))
// }

// // last_checkpointed_operation 翻译怎么翻的
// method CAcceptorInit(rcs:CReplicaConstants) returns (acceptor:AcceptorState)
// requires CReplicaConstansValid(rcs)
//   ensures NextAcceptorState_InitPostconditions(acceptor, rcs)
// {
//   var max_ballot := CBallot(0, 0);
//   var votes := CVotes(map []);
//   var last_checkpointed_operation := seq<COperationNumber>(|rcs.all.config.replica_ids|, i => 0);
//   var log_truncation_point := 0;
//   acceptor := AcceptorState(
//     rcs, max_ballot, votes, last_checkpointed_operation,  log_truncation_point);

//   lemma_CAcceptorInit(rcs, acceptor);
// }

// lemma {:axiom} lemma_CAcceptorInit(rcs:CReplicaConstants, acceptor:AcceptorState)
// requires CReplicaConstansValid(rcs)
//   ensures NextAcceptorState_InitPostconditions(acceptor, rcs)

// method CAcceptorProcess1a(acceptor:AcceptorState, inp:CPacket) returns (acceptor':AcceptorState, packets_sent:CBroadcast)
// requires inp.msg.CMessage_1a?
// requires CReplicaConstansValid(acceptor.constants)
// {
//   var in_msg := inp.msg;
//   var a := CBalLt(acceptor.maxBallot, in_msg.bal_1a);
//   // var b := CReplicaConstansValid(acceptor.constants);
//   if &&(inp.src in acceptor.constants.all.config.replica_ids)
//     && a {
//     packets_sent := CBroadcast(acceptor.constants.all.config.replica_ids[acceptor.constants.my_index], 
//                             [inp.src], CMessage_1b(in_msg.bal_1a, acceptor.log_truncation_point, acceptor.votes));
//     acceptor' := acceptor.(maxBallot := in_msg.bal_1a);
//   } else {
//     acceptor' := acceptor;
//     packets_sent := CBroadcastNop;
//   }
// }

// // 怎么翻译？？？
// // acceptor'的成员不能直接赋值
// // run-time check
// method CAcceptorProcess2a(acceptor:AcceptorState, inp:CPacket) returns (acceptor':AcceptorState, packets_sent:CBroadcast)
// requires AcceptorIsValid(acceptor)
// requires inp.msg.CMessage_2a?
// // requires inp.src in acceptor.constants.all.config.replica_ids
// // requires CBalLeq(acceptor.maxBallot, inp.msg.bal_2a)
// // requires CLeqUpperBound( inp.msg.opn_2a, acceptor.constants.all.params.max_integer_val)
// {
//   var in_msg := inp.msg;
//   var newLogTruncationPoint:uint64 := 0;
//   // if ((in_msg.opn_2a - acceptor.constants.all.params.max_log_length + 1) as uint64 > acceptor.log_truncation_point) 

//   /*

//   Origin: 
//     if ((in_msg.opn_2a - acceptor.constants.all.params.max_log_length + 1) as uint64 > acceptor.log_truncation_point) {}

//   Problem: 
//     Have to provide runtime error check for '(in_msg.opn_2a - acceptor.constants.all.params.max_log_length + 1)'

//   Solution 1:
//     在编写spec时拆开if的逻辑，继续行对行翻译
//     if 
//       && acceptor.constants.all.params.max_log_length >= 1
//       && in_msg.opn_2a > acceptor.constants.all.params.max_log_length - 1
//       && (in_msg.opn_2a - acceptor.constants.all.params.max_log_length + 1) > acceptor.log_truncation_point)

//   Solution 2:
//     翻译器自动生成 (之前的问题通过加HINT解决：uint64不溢出，)

//   */



//   // // acceptor.constants.all.params.max_log_length - 1 > 0
//   // // in_msg.opn_2a > (acceptor.constants.all.params.max_log_length - 1)
//   // // assert acceptor.constants.all.params.max_integer_val > acceptor.constants.all.params.max_log_length > 0;
//   // var maxLogLengthMinus1:uint64 := (acceptor.constants.all.params.max_log_length - 1 as uint64) as uint64;
//   // // var a : uint64 := in_msg.opn_2a;
//   // // Error: destructor 'opn_2a' can only be applied to datatype values constructed by 'CMessage_2a'
//   // if in_msg.opn_2a >= maxLogLengthMinus1
//   // {
//   //   var potentialNewTruncationPoint:uint64 := in_msg.opn_2a - maxLogLengthMinus1;
//   //   if potentialNewTruncationPoint > acceptor.log_truncation_point{
//   //     newLogTruncationPoint := (in_msg.opn_2a - acceptor.constants.all.params.max_log_length + 1) as uint64;
//   //   } else {
//   //     newLogTruncationPoint := acceptor.log_truncation_point;
//   //   }
//   // } else {
//   //     newLogTruncationPoint := acceptor.log_truncation_point;
//   // }

//   // var maxLogLengthMinus1:uint64 := inp.msg.opn_2a - acceptor.constants.all.params.max_log_length + 1;
//   // if(maxLogLengthMinus1 > acceptor.log_truncation_point){
//   //     newLogTruncationPoint := (in_msg.opn_2a - acceptor.constants.all.params.max_log_length + 1) as uint64;
//   // } else {
//   //     newLogTruncationPoint := acceptor.log_truncation_point;
//   // }

//   if inp.msg.opn_2a > acceptor.log_truncation_point + acceptor.constants.all.params.max_log_length - 1 
//   {
//     newLogTruncationPoint := (in_msg.opn_2a - acceptor.constants.all.params.max_log_length + 1) as uint64;
//   } else {
//      newLogTruncationPoint := acceptor.log_truncation_point;
//   }
//   packets_sent := BuildBroadcastToEveryone(acceptor.constants.all.config, acceptor.constants.my_index, CMessage_2b(in_msg.bal_2a, in_msg.opn_2a, in_msg.val_2a));
//   if(acceptor.log_truncation_point <= in_msg.opn_2a) {
//     var newvotes := CAddVoteAndRemoveOldOnes(acceptor.votes, CVote(in_msg.bal_2a, in_msg.val_2a), in_msg.opn_2a,  newLogTruncationPoint);
//     // acceptor'.votes := newvotes;
//     acceptor' := acceptor.(votes := newvotes, maxBallot := in_msg.bal_2a, log_truncation_point := newLogTruncationPoint);
//   } else {
//     // acceptor'.votes := acceptor.votes;
//     acceptor' := acceptor.(maxBallot := in_msg.bal_2a, log_truncation_point := newLogTruncationPoint);
//   }
  
//   // acceptor'.constants := acceptor.constants;
//   // acceptor'.last_checkpointed_operation := acceptor.last_checkpointed_operation;
// }

// // method mname(state, var) returns (state')
// method CAcceptorProcessHeartbeat(acceptor:AcceptorState, inp:CPacket) returns (acceptor':AcceptorState)
// requires AcceptorIsValid(acceptor)
// requires inp.msg.CMessage_Heartbeat?
// {
//   // if exp {stmt} else {stmt}
//   if inp.src in acceptor.constants.all.config.replica_ids {
//     // var := exp
//     var sender_index := CGetReplicaIndex(inp.src, acceptor.constants.all.config);
//     if 0 <= sender_index as int < |acceptor.last_checkpointed_operation| && inp.msg.opn_ckpt > acceptor.last_checkpointed_operation[sender_index] {
//       // state' := state.(var := var)
//       acceptor' := acceptor.(last_checkpointed_operation:= acceptor.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt]);
//     } else {
//       acceptor' := acceptor;
//       // state' := state
//     }
//   } else {
//     acceptor' := acceptor;
//   }
// }

// // stmt
// // var := var 

// method CAcceptorTruncateLog(acceptor:AcceptorState, opn:COperationNumber) returns (acceptor':AcceptorState)
// requires AcceptorIsValid(acceptor)
// {
//   if opn <= acceptor.log_truncation_point {
//     acceptor' := acceptor;
//   } else {
//     var truncatedVotes := CRemoveVotesBeforeLogTruncationPoint(acceptor.votes, opn);
//     acceptor' := acceptor.(log_truncation_point := opn,
//                            votes := truncatedVotes);
//   }
// }

} 
