include "AppInterface.i.dfy"
include "../../Protocol/RSL/Proposer.i.dfy"
include "ElectionImpl.i.dfy"
include "Broadcast.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Protocol/RSL/Proposer.i.dfy"
include "ElectionImpl.i.dfy"
include "CConstants.i.dfy"
include "../../Common/Collections/Assumes.i.dfy"

module LiveRSL__ProposerModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveRSL__AppInterface_i
  import opened LiveRSL__Broadcast_i
  import opened LiveRSL__CMessage_i
  import opened LiveRSL__CMessageRefinements_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__ConstantsState_i
  import opened LiveRSL__CPaxosConfiguration_i
  import opened LiveRSL__CTypes_i
  import opened LiveRSL__Election_i
  import opened LiveRSL__ElectionModel_i
  import opened LiveRSL__Message_i
  import opened LiveRSL__PacketParsing_i
  import opened LiveRSL__Proposer_i
  import opened LiveRSL__Types_i
  import opened Impl__LiveRSL__Broadcast_i
  import opened Collections__Maps_i
  import opened Collections__Sets_i
  import opened Common__NodeIdentity_i
  import opened Common__SeqIsUnique_i
  import opened Common__SeqIsUniqueDef_i
  import opened Common__UdpClient_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened GenericRefinement_i
  import opened Environment_s
  import opened LiveRSL__Environment_i
  import opened Common_Assume_i
  // import opened LiveRSL__Proposer_i

/************************** AutoMan Translation ************************/
	datatype CIncompleteBatchTimer = 
	CIncompleteBatchTimerOn(
		when: int
	)
	 | 
	CIncompleteBatchTimerOff(
		
	)

	predicate CIncompleteBatchTimerIsValid(s: CIncompleteBatchTimer) 
	{
		match s
		case CIncompleteBatchTimerOn(when) => CIncompleteBatchTimerIsAbstractable(s)
		case CIncompleteBatchTimerOff() => CIncompleteBatchTimerIsAbstractable(s)

	}

	predicate CIncompleteBatchTimerIsAbstractable(s: CIncompleteBatchTimer) 
	{
		match s
		case CIncompleteBatchTimerOn(when) => true
		case CIncompleteBatchTimerOff() => true

	}

	function AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(s: CIncompleteBatchTimer) : IncompleteBatchTimer 
		requires CIncompleteBatchTimerIsAbstractable(s)
	{
		match s
		case CIncompleteBatchTimerOn(when) => IncompleteBatchTimerOn(s.when)
		case CIncompleteBatchTimerOff => IncompleteBatchTimerOff()

	}

  datatype CProposer = 
	CProposer(
		constants: CReplicaConstants, 
		current_state: int, 
		request_queue: seq<CRequest>, 
		max_ballot_i_sent_1a: CBallot, 
		next_operation_number_to_propose: int, 
		received_1b_packets: set<CPacket>, 
		highest_seqno_requested_by_client_this_view: map<EndPoint, int>, 
		incomplete_batch_timer: CIncompleteBatchTimer, 
		election_state: CElectionState,

    /** I1 */
    maxOpnWithProposal:COperationNumber,

    maxLogTruncationPoint:COperationNumber
	)

  predicate MaxOpnWithProposalInVotes(proposer:CProposer)
  {
    forall p :: p in proposer.received_1b_packets && p.msg.CMessage_1b? ==> MaxOpnWithProposal(proposer, p.msg.votes)
  }

  predicate MaxOpnWithProposal(proposer:CProposer, votes:CVotes)
  {
    forall opn :: opn in votes ==> opn < proposer.maxOpnWithProposal
  }

  predicate MaxLogTruncationPoint(proposer:CProposer)
  {
    forall p :: p in proposer.received_1b_packets && p.msg.CMessage_1b? ==> p.msg.log_truncation_point <= proposer.maxLogTruncationPoint
  }


	predicate CProposerIsValid(s: CProposer) 
	{
		CProposerIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		(forall i :: i in s.request_queue ==> CRequestIsValid(i)) 
		&& 
		CBallotIsValid(s.max_ballot_i_sent_1a) 
		&& 
		(forall i :: i in s.received_1b_packets ==> CPacketIsValid(i)) 
		&& 
		(forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsValid(i)) 
		&& 
		CIncompleteBatchTimerIsValid(s.incomplete_batch_timer) 
		&& 
		CElectionStateIsValid(s.election_state)
    /** Manually Added */
    &&
    SetIsInjective(s.received_1b_packets, AbstractifyCPacketToRslPacket)
    &&
    (forall p :: p in s.received_1b_packets ==>
                   && CPacketIsValid(p)
                   && p.msg.CMessage_1b?
                   && p.msg.bal_1b == s.max_ballot_i_sent_1a
                   && CVotesIsValid(p.msg.votes))
    &&
    s.constants == s.election_state.constants
    &&
    CRequestBatchIsValid(s.request_queue)

    && (s.current_state == 2 ==> MaxOpnWithProposalInVotes(s))
    && (s.current_state == 2 ==> MaxLogTruncationPoint(s))
	}

	predicate CProposerIsAbstractable(s: CProposer) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		(forall i :: i in s.request_queue ==> CRequestIsAbstractable(i)) 
		&& 
		CBallotIsAbstractable(s.max_ballot_i_sent_1a) 
		&& 
		(forall i :: i in s.received_1b_packets ==> CPacketIsAbstractable(i)) 
		&& 
		(forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsAbstractable(i)) 
		&& 
		CIncompleteBatchTimerIsAbstractable(s.incomplete_batch_timer) 
		&& 
		CElectionStateIsAbstractable(s.election_state)
	}

  function AbstractifyCProposerToLProposer(s: CProposer) : LProposer 
    requires CProposerIsValid(s)
		// requires CProposerIsAbstractable(s)
	{
		LProposer(
      AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), 
      s.current_state, 
      AbstractifySeq(s.request_queue, AbstractifyCRequestToRequest), 
      AbstractifyCBallotToBallot(s.max_ballot_i_sent_1a), 
      s.next_operation_number_to_propose, 
      AbstractifySet(s.received_1b_packets, AbstractifyCPacketToRslPacket), 
      AbstractifyMap(s.highest_seqno_requested_by_client_this_view, AbstractifyEndPointToNodeIdentity, NoChange, AbstractifyNodeIdentityToEndPoint), 
      AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(s.incomplete_batch_timer), 
      AbstractifyCElectionStateToElectionState(s.election_state))
	}
function method CIsAfterLogTruncationPoint(
    opn : COperationNumber ,
    received_1b_packets : set<CPacket>) : bool
    /*
    requires COperationNumberIsValid(opn)
    requires (forall i :: i in received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
    ensures var bc := CIsAfterLogTruncationPoint(opn, received_1b_packets); var bl := LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket)); bl == bc
    */
  {
    (forall p :: p in received_1b_packets && p.msg.CMessage_1b? ==> p.msg.log_truncation_point <= opn)
  }

  function method CSetOfMessage1b(
    S : set<CPacket>) : bool
    /*
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    ensures var bc := CSetOfMessage1b(S); var bl := LSetOfMessage1b(AbstractifySet(S, AbstractifyCPacketToRslPacket)); bl == bc
    */
  {
    forall p :: p in S ==> p.msg.CMessage_1b?
  }

  function method CSetOfMessage1bAboutBallot(
    S : set<CPacket> ,
    b : CBallot) : bool
    /*
      requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires CBallotIsValid(b)
    ensures var bc := CSetOfMessage1bAboutBallot(S, b); var bl := LSetOfMessage1bAboutBallot(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCBallotToBallot(b)); bl == bc
      */
  {

    &&
      CSetOfMessage1b(S)
    &&
      (forall p :: p in S ==> p.msg.bal_1b == b)
  }

  /* ----------------------------------------- */

  function method {:opaque} CAllAcceptorsHadNoProposal(
    S : set<CPacket> ,
            opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CAllAcceptorsHadNoProposal(S, opn); var bl := LAllAcceptorsHadNoProposal(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    forall p :: p in S ==> !(opn in p.msg.votes)
  }

  function method CExistVotesHasProposalLargeThanOpn(
    p : CPacket ,
    op : COperationNumber) : bool
    requires p.msg.CMessage_1b?
    requires CPacketIsValid(p)
    ensures var bc := CExistVotesHasProposalLargeThanOpn(p, op); var bl := LExistVotesHasProposalLargeThanOpn(AbstractifyCPacketToRslPacket(p), AbstractifyCOperationNumberToOperationNumber(op)); bl == bc
  {
    exists opn :: opn in p.msg.votes && opn > op
  }

  function method CExistsAcceptorHasProposalLargeThanOpn(
    S : set<CPacket> ,
    op : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(op)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CExistsAcceptorHasProposalLargeThanOpn(S, op); var bl := LExistsAcceptorHasProposalLargeThanOpn(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(op)); bl == bc
  {
    exists p :: p in S && CExistVotesHasProposalLargeThanOpn(p, op)
  }

  function method Cmax_balInS(
    c : CBallot ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CBallotIsValid(c)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := Cmax_balInS(c, S, opn); var bl := Lmax_balInS(AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    forall p :: p in S && opn in p.msg.votes ==> CBalLeq(p.msg.votes[opn].max_value_bal, c)
  }

  function method CExistsBallotInS(
    v : CRequestBatch ,
    c : CBallot ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CRequestBatchIsValid(v)
    requires CBallotIsValid(c)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CExistsBallotInS(v, c, S, opn); var bl := LExistsBallotInS(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    exists p ::  && p in S && opn in p.msg.votes && p.msg.votes[opn].max_value_bal == c && p.msg.votes[opn].max_val == v
  }

  function method CValIsHighestNumberedProposalAtBallot(
    v : CRequestBatch ,
    c : CBallot ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CRequestBatchIsValid(v)
    requires CBallotIsValid(c)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CValIsHighestNumberedProposalAtBallot(v, c, S, opn); var bl := LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {

    &&
      Cmax_balInS(c, S, opn)
    &&
      CExistsBallotInS(v, c, S, opn)
  }

  function method CValIsHighestNumberedProposal(
    v : CRequestBatch ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CRequestBatchIsValid(v)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CValIsHighestNumberedProposal(v, S, opn); var bl := LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    // exists c :: CValIsHighestNumberedProposalAtBallot(v, c, S, opn)
    /* Manually added */
    exists p :: p in S && opn in p.msg.votes && CValIsHighestNumberedProposalAtBallot(v, p.msg.votes[opn].max_value_bal, S, opn)
  }

  function method CProposerCanNominateUsingOperationNumber(
    s : CProposer ,
    log_truncation_point : COperationNumber ,
    opn : COperationNumber) : bool
    requires CProposerIsValid(s)
    requires COperationNumberIsValid(log_truncation_point)
    requires COperationNumberIsValid(opn)
    ensures var bc := CProposerCanNominateUsingOperationNumber(s, log_truncation_point, opn); var bl := LProposerCanNominateUsingOperationNumber(AbstractifyCProposerToLProposer(s), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {

    &&
      s.election_state.current_view == s.max_ballot_i_sent_1a
    &&
      s.current_state == 2
    &&
      |s.received_1b_packets| >= CMinQuorumSize(s.constants.all.config)
    &&
      CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
    &&
      CIsAfterLogTruncationPoint(opn, s.received_1b_packets)
    &&
      opn < UpperBoundedAdditionImpl(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val)
    &&
      opn >= 0
    &&
      CLtUpperBound(opn, s.constants.all.params.max_integer_val)
  }


  function method CProposerInit(c: CReplicaConstants) : CProposer 
		requires CReplicaConstantsIsValid(c)
		// requires CWellFormedLConfiguration(c.all.config)
		ensures var s := CProposerInit(c); CProposerIsValid(s) && LProposerInit(AbstractifyCProposerToLProposer(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			0; 		
		var t3 := 
			[]; 		
		var t4 := 
			CBallot(0, c.my_index); 		
		var t5 := 
			0; 		
		var t6 := 
			{}; 		
		var t7 := 
			map[]; 		
		var t8 := 
			CElectionStateInit(c); 		
		var t9 := 
			CIncompleteBatchTimerOff(); 		
		CProposer(t1, t2, t3, t4, t5, t6, t7, t9, t8, 0, 0)
	}

  /** 12 lines manual modification for I1 */
  method CProposerProcessRequest(
    s : CProposer ,
    packet : CPacket,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer)
    requires packet.msg.CMessage_Request?
    requires CProposerIsValid(s)
    requires CPacketIsValid(packet)

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

    // ensures var s' := CProposerProcessRequest(s, packet); 
    ensures CProposerIsValid(s') 
    ensures LProposerProcessRequest(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(packet))
  {
    var val := CRequest(packet.src, packet.msg.seqno_req, packet.msg.val);

    var election := CElectionStateReflectReceivedRequest_I1(s.election_state, val, cur_req_set, prev_req_set);

    lemma_AbstractifyMap_properties(s.highest_seqno_requested_by_client_this_view, AbstractifyEndPointToNodeIdentity, int_to_int, AbstractifyNodeIdentityToEndPoint);
    // var s' :=
      if  && s.current_state != 0 && ( val.client !in s.highest_seqno_requested_by_client_this_view || val.seqno > s.highest_seqno_requested_by_client_this_view[val.client])
      {
        s' := s.(
        election_state := election,
        request_queue := s.request_queue + [val],
        highest_seqno_requested_by_client_this_view := s.highest_seqno_requested_by_client_this_view[val.client := val.seqno]
        );
      }
      else
      {
        s' := s.(
        election_state := election
        )
      ;
      }
    lemma_RequestQueue_len(s'.request_queue);
    // s'
    lemma_CProposerProcessRequest(s, packet, s');
  }

  lemma {:axiom} lemma_CProposerProcessRequest(s : CProposer ,
    packet : CPacket,s':CProposer)
    requires packet.msg.CMessage_Request?
    requires CProposerIsValid(s)
    requires CPacketIsValid(packet)
    ensures CProposerIsValid(s') 
    ensures LProposerProcessRequest(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(packet))

  function method CProposerMaybeEnterNewViewAndSend1a(s: CProposer) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		ensures var (s', broadcast_sent_packets) := CProposerMaybeEnterNewViewAndSend1a(s); CProposerIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LProposerMaybeEnterNewViewAndSend1a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := 
			if s.election_state.current_view.proposer_id == s.constants.my_index && CBalLt(s.max_ballot_i_sent_1a, s.election_state.current_view) then 
				var t1 := 
					s.(current_state := 1, max_ballot_i_sent_1a := s.election_state.current_view, received_1b_packets := {}, highest_seqno_requested_by_client_this_view := map[], request_queue := s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch); 				
				var t2 := 
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1a(s.election_state.current_view))); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
          Broadcast(CBroadcastNop);
					// []; 				
				(t1, t2); 	
    lemma_RequestQueue_len(t1.0.request_queue);
		(t1.0, t1.1)
	}

  function method CProposerProcess1b(s: CProposer, p: CPacket) : CProposer 
		requires CProposerIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_1b?
		requires p.src in s.constants.all.config.replica_ids
		requires p.msg.bal_1b == s.max_ballot_i_sent_1a
		requires s.current_state == 1
		requires (forall other_packet :: other_packet in s.received_1b_packets ==> other_packet.src != p.src)
		ensures var s' := CProposerProcess1b(s, p); CProposerIsValid(s') && LProposerProcess1b(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p))
	{
    /* Manually added */
    ghost var s_ := AbstractifyCProposerToLProposer(s);
    ghost var s'_ := s_.(received_1b_packets := s_.received_1b_packets + { AbstractifyCPacketToRslPacket(p) });
		var t1 := 
			s.(received_1b_packets := s.received_1b_packets + {p}); 	
    assert AbstractifyCProposerToLProposer(t1).received_1b_packets == s'_.received_1b_packets;	
		t1
	}

  // function method CProposerMaybeEnterPhase2(
  //   s : CProposer ,
  //   log_truncation_point : COperationNumber) : (CProposer, OutboundPackets)
  //   requires CProposerIsValid(s)
  //   requires COperationNumberIsValid(log_truncation_point)
  //   ensures var (s', sent_packets) := CProposerMaybeEnterPhase2(s, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(sent_packets) && LProposerMaybeEnterPhase2(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
  // {
  //   if  && |s.received_1b_packets| >= CMinQuorumSize(s.constants.all.config) && CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) && s.current_state == 1
  //   then
  //     (
  //       s.(
  //       current_state := 2,
  //       next_operation_number_to_propose := log_truncation_point
  //       ),
  //       Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_StartingPhase2(s.max_ballot_i_sent_1a, log_truncation_point)))
  //     )
  //   else
  //     (
  //       s,
  //       Broadcast(CBroadcastNop)
  //     )
  // }

lemma lemma_MapSingleton<T(!new),S(!new)>(m:map<T,S>, elm:T)
  requires |m| == 1
  requires elm in m
  ensures forall x :: x in m ==> x == elm
{
  var empty := RemoveElt(m, elm);
}

method getMaxOpnWithProposalFromSingleton(m:map<COperationNumber,CVote>) returns (maxOpn:COperationNumber)
  requires |m| > 0
  ensures forall opn :: opn in m ==> opn <= maxOpn
{
  if |m| == 1 
  {
    var opn :| opn in m;
    lemma_MapSingleton(m, opn);
    assert forall op :: op in m ==> op == opn;
    maxOpn := opn;
  } else {
    var opn :| opn in m;
    var rest := RemoveElt(m, opn);
    var restMax:COperationNumber;
        
    restMax := getMaxOpnWithProposalFromSingleton(rest);
    if (restMax > opn) {
      maxOpn := restMax;
    } else {
      maxOpn := opn;
    }
  }
}

method getMaxOpnWithProposalFromSet(s:set<CPacket>) returns (maxOpn:COperationNumber, foundNonEmpty:bool)
  requires forall p :: p in s ==> p.msg.CMessage_1b? && CVotesIsValid(p.msg.votes)
  requires |s| > 0
  ensures forall p :: p in s ==> (forall opn :: opn in p.msg.votes ==> opn <= maxOpn)
  ensures foundNonEmpty <==> exists p :: p in s && |p.msg.votes| > 0
{
  if |s| == 1 
  {
    var p :| p in s;
    assert p.msg.CMessage_1b?;
            
    forall q | q in s 
      ensures q == p
    {
      ThingsIKnowAboutASingletonSet(s, q, p);
    }
    if (|p.msg.votes| > 0) {
      maxOpn := getMaxOpnWithProposalFromSingleton(p.msg.votes);
      foundNonEmpty := true;
    } else {
      maxOpn := 0;
      foundNonEmpty := false;
    }
  } else {
    var p :| p in s;
    var rest := s - {p};
    var candidateOpn;
    var foundLocal:bool;
    if (|p.msg.votes| > 0) {
      candidateOpn := getMaxOpnWithProposalFromSingleton(p.msg.votes);
      foundLocal := true;
      assert forall opn :: opn in p.msg.votes ==> opn <= candidateOpn;
    } else {
      candidateOpn := 0;
      foundLocal := false;
    }
    forall x | x in rest 
      ensures x.msg.CMessage_1b? && CVotesIsValid(x.msg.votes)
    {
      assert x in s;
      assert forall q :: q in s ==> q.msg.CMessage_1b? && CVotesIsValid(q.msg.votes);
    }
        
    var restMaxOpn, foundTemp  := getMaxOpnWithProposalFromSet(rest);
    if (foundTemp || foundLocal) {
      foundNonEmpty := true;
    } else {
      foundNonEmpty := false;
    }
    if candidateOpn > restMaxOpn {
      maxOpn := candidateOpn;
    } else {
      maxOpn := restMaxOpn;
    }
  }
}


method getMaxLogTruncationPoint(s:set<CPacket>) returns (maxLogTruncationPoint:COperationNumber)
  requires forall p :: p in s ==> p.msg.CMessage_1b?
  requires |s| > 0
  ensures forall p :: p in s ==> p.msg.log_truncation_point <= maxLogTruncationPoint
{
  if |s| == 1 
  {
    var p :| p in s;
    assert p.msg.CMessage_1b?;
            
    forall q | q in s 
      ensures q == p
    {
      ThingsIKnowAboutASingletonSet(s, q, p);
    }
    maxLogTruncationPoint := p.msg.log_truncation_point;
  } else {
    var p :| p in s;
    var rest := s - {p};
    var candidateOpn := p.msg.log_truncation_point;
    forall x | x in rest 
      ensures x.msg.CMessage_1b?
    {
      assert x in s;
      assert forall q :: q in s ==> q.msg.CMessage_1b?;
    }

    var restMaxOpn := getMaxLogTruncationPoint(rest);
    if candidateOpn > restMaxOpn {
      maxLogTruncationPoint := candidateOpn;
    } else {
      maxLogTruncationPoint := restMaxOpn;
    }
  }
}


method {:timeLimitMultiplier 8} CProposerMaybeEnterPhase2(proposer:CProposer,log_truncation_point:COperationNumber) 
  returns (proposer':CProposer, sent_packets:OutboundPackets)
  requires CProposerIsValid(proposer)
  requires COperationNumberIsAbstractable(log_truncation_point)
  ensures  CProposerIsValid(proposer')
  ensures  OutboundPacketsIsValid(sent_packets)
  ensures  OutboundPacketsHasCorrectSrc(sent_packets, proposer.constants.all.config.replica_ids[proposer.constants.my_index])
  ensures  LProposerMaybeEnterPhase2(AbstractifyCProposerToLProposer(proposer), AbstractifyCProposerToLProposer(proposer'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
  ensures proposer.constants == proposer'.constants
  ensures proposer'.election_state.cur_req_set  == proposer.election_state.cur_req_set
  ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set
{
  // var start_time := Time.GetDebugTimeTicks();
  assert SetOfInjectiveTypeCPackets(proposer.received_1b_packets);
  ghost var ref_proposer  := AbstractifyCProposerToLProposer(proposer);
  // lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
  assert |proposer.received_1b_packets| == |AbstractifySetOfCPacketsToSetOfRslPackets(proposer.received_1b_packets)|;
  var quorum_size := CMinQuorumSize(proposer.constants.all.config);
  // The following is already true thanks to our IsValid invariant:
  //    assert LSet(ref_proposer.received_1b_packets, ref_proposer.max_ballot_i_sent_1a);
  // lemma_Received1bBound(proposer);
  if |proposer.received_1b_packets| >= quorum_size && proposer.current_state == 1 {
    assert |ref_proposer.received_1b_packets| >= LMinQuorumSize(ref_proposer.constants.all.config);
    assert LSetOfMessage1bAboutBallot(ref_proposer.received_1b_packets, ref_proposer.max_ballot_i_sent_1a);
    assert ref_proposer.current_state == 1;

    var maxOpn, foundNonEmpty := getMaxOpnWithProposalFromSet(proposer.received_1b_packets);
    if !foundNonEmpty {
      maxOpn := 0;
    } else {
      maxOpn := maxOpn + 1;
    }
        
    var maxLogTP := getMaxLogTruncationPoint(proposer.received_1b_packets);
    //print("Proposer starting phase 2 for ballot", proposer.max_ballot_i_sent_1a, ". Setting maxOpnWithProposal to ", maxOpn, " and maxLogTruncationPoint to", maxLogTP, "\n");
    proposer' := proposer.(current_state := 2, next_operation_number_to_propose := log_truncation_point, maxOpnWithProposal := maxOpn, maxLogTruncationPoint := maxLogTP);
    var msg := CMessage_StartingPhase2(proposer.max_ballot_i_sent_1a, log_truncation_point);
    assert Marshallable(msg);
    sent_packets := Broadcast(BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, msg));
    // var end_time := Time.GetDebugTimeTicks();
    // RecordTimingSeq("ProposerMaybeEnterPhase2_work", start_time, end_time);
  } else {
    proposer' := proposer;
    sent_packets := Broadcast(CBroadcastNop);
    // lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer({});
    // var end_time := Time.GetDebugTimeTicks();
    // RecordTimingSeq("ProposerMaybeEnterPhase2_nada", start_time, end_time);
  }

  ghost var ref_proposer' := AbstractifyCProposerToLProposer(proposer');
  ghost var ref_logTruncationPoint := AbstractifyCOperationNumberToOperationNumber(log_truncation_point);
}


  /** 5 lines manual code for I1 */
  function method CProposerNominateNewValueAndSend2a(
    s : CProposer ,
    clock : int ,
    log_truncation_point : COperationNumber) : (CProposer, OutboundPackets)
    requires CProposerIsValid(s)
    requires COperationNumberIsValid(log_truncation_point)
    requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
    requires CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    ensures var (s', sent_packets) := CProposerNominateNewValueAndSend2a(s, clock, log_truncation_point); 
    CProposerIsValid(s') && OutboundPacketsIsValid(sent_packets) && LProposerNominateNewValueAndSend2a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
    && s.election_state == s'.election_state
  {
    var batchSize := if |s.request_queue| <= s.constants.all.params.max_batch_size || s.constants.all.params.max_batch_size < 0 then |s.request_queue| else s.constants.all.params.max_batch_size;
    var v := s.request_queue[..batchSize];
  
    /* Manually added */
    lemma_seq_sub(s.request_queue, AbstractifyCRequestToRequest, 0, batchSize);

    var opn := s.next_operation_number_to_propose;
    (
      s.(
      request_queue := s.request_queue[batchSize..],
      next_operation_number_to_propose := s.next_operation_number_to_propose + 1,
      incomplete_batch_timer := if |s.request_queue| > batchSize then CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)) else CIncompleteBatchTimerOff()
      ),
      Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2a(s.max_ballot_i_sent_1a, opn, v)))
    )
  }


  // function method CProposerNominateNewValueAndSend2a(s: CProposer, clock: int, log_truncation_point: COperationNumber) : (CProposer, OutboundPackets) 
	// 	requires CProposerIsValid(s)
	// 	requires COperationNumberIsValid(log_truncation_point)
	// 	requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
	// 	requires CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
	// 	ensures var (s', broadcast_sent_packets) := CProposerNominateNewValueAndSend2a(s, clock, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LProposerNominateNewValueAndSend2a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	// {
  //   var batchSize := 
	// 			if (|s.request_queue| <= s.constants.all.params.max_batch_size) || (s.constants.all.params.max_batch_size < 0) then 
	// 				|s.request_queue| 
	// 			else 
	// 				s.constants.all.params.max_batch_size; 	
	// 	var t1 := 
	// 		var t1 := 
	// 			var v := 
	// 				s.request_queue[ .. batchSize]; 				
	// 			var t1 := 
	// 				var opn := 
	// 					s.next_operation_number_to_propose; 					
	// 				var t1 := 
	// 					s.(
  //             request_queue := s.request_queue[batchSize .. ], 
  //             next_operation_number_to_propose := s.next_operation_number_to_propose + 1, 
  //             incomplete_batch_timer := 
  //               if |s.request_queue| > batchSize then 
  //                 CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)) 
  //               else 
  //                 CIncompleteBatchTimerOff()); 					
	// 				var t2 := 
  //           /** Manually Modified */
	// 					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2a(s.max_ballot_i_sent_1a, opn, v))); 					
	// 				(t1, t2); 				
	// 			(t1.1, t1.0); 			
	// 		(t1.1, t1.0); 	
  //     /* Manually added */
  //     lemma_seq_sub(s.request_queue, AbstractifyCRequestToRequest, 0, batchSize);	
	// 	(t1.0, t1.1)
	// }

  method CProposerProcessHeartbeat(
		s : CProposer ,
		p : CPacket ,
		clock : int,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>
    ) returns (s':CProposer)
		requires CProposerIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_Heartbeat?
    
    // requires p.src in s.constants.all.config.replica_ids
    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

		// ensures var s' := CProposerProcessHeartbeat(s, p, clock);
    ensures CProposerIsValid(s') && LProposerProcessHeartbeat(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p), clock)
	{
    /* Manually added to pass the Temporal Relation */
    var election := CElectionStateProcessHeartbeat(s.election_state, p, clock, cur_req_set, prev_req_set);
    
    var ss' := s.(election_state := election);


		if CBalLt(s.election_state.current_view, ss'.election_state.current_view)
		{ 
			s' := s.(
				election_state := election,
				current_state := 0,
				request_queue := []
			);
    }
		else 
    {
			s' := s.(
				election_state := election,
				current_state := s.current_state,
				request_queue := s.request_queue
			);
    }
	}

  // /** 10 lines manual modification for I1 */
  // method CProposerProcessHeartbeat(s: CProposer, p: CPacket, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer)
	// 	requires CProposerIsValid(s)
	// 	requires CPacketIsValid(p)
	// 	requires p.msg.CMessage_Heartbeat?
  //   /** Manually Added for I1 */
	// 	// requires p.src in s.constants.all.config.replica_ids
  //   requires cur_req_set != prev_req_set
  //   requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
  //   requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
  //   modifies cur_req_set, prev_req_set
  //   ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
  //   ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

  //   ensures CProposerIsValid(s') && LProposerProcessHeartbeat(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p), clock)
	// {
	// 	var t1 := 
	// 		CElectionStateProcessHeartbeat(s.election_state, p, clock, cur_req_set, prev_req_set);
	// 	var t2 := 
  //     if CBalLt(s.election_state.current_view, t1.current_view) then 
	// 			var t1 := 
	// 				0; 				
	// 			var t2 := 
	// 				[]; 				
	// 			(t1, t2) 
  //     else
	// 			var t1 := 
	// 				s.current_state; 				
	// 			var t2 := 
	// 				s.request_queue; 				
	// 			(t1, t2);
	// 	// var t3 := 
	// 		s' := s.(election_state := t1, current_state := t2.0, request_queue := t2.1); 
	// 	// t3
	// }

  /** 8 lines manual code for I1 */
  method CProposerCheckForViewTimeout(s: CProposer, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer)
		requires CProposerIsValid(s)
		 
    /** Manually Added for I1 */
    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

    ensures CProposerIsValid(s') && LProposerCheckForViewTimeout(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	{
		var t1 := 
			CElectionStateCheckForViewTimeout(s.election_state, clock, cur_req_set, prev_req_set); 		
	  s' := 
			s.(election_state := t1); 		
	}

  method CProposerCheckForQuorumOfViewSuspicions(
		s : CProposer ,
		clock : int,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer)
		requires CProposerIsValid(s)

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

		// ensures var s' := CProposerCheckForQuorumOfViewSuspicions(s, clock); 
    ensures CProposerIsValid(s') && LProposerCheckForQuorumOfViewSuspicions(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	{

    /* Manually added to pass the Temporal Relation */
    var election := CElectionStateCheckForQuorumOfViewSuspicions(s.election_state, clock, cur_req_set, prev_req_set);
    var ss' := s.(election_state := election);

		if CBalLt(s.election_state.current_view, ss'.election_state.current_view)
		{ 
			s' := s.(
				election_state := election,
				current_state := 0,
				request_queue := []
			);
    }
		else 
    {
			s' := s.(
				election_state := election,
				current_state := s.current_state,
				request_queue := s.request_queue
			);
    }
	}

  // /** 8 lines manual code for I1 */
  // method CProposerCheckForQuorumOfViewSuspicions(s: CProposer, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer)
	// 	requires CProposerIsValid(s)
		
  //   /** Manually Added for I1 */
  //   requires cur_req_set != prev_req_set
  //   requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
  //   requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
  //   modifies cur_req_set, prev_req_set
  //   ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
  //   ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

  //   ensures CProposerIsValid(s') && LProposerCheckForQuorumOfViewSuspicions(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	// {
	// 	var t1 := 
	// 		CElectionStateCheckForQuorumOfViewSuspicions(s.election_state, clock, cur_req_set, prev_req_set); 		
	// 	var t2 := 
  //     if CBalLt(s.election_state.current_view, t1.current_view) then
	// 			var t1 := 
	// 				0; 				
	// 			var t2 := 
	// 				[]; 				
	// 			(t1, t2) 
	// 		else 
	// 			var t1 := 
	// 				s.current_state; 				
	// 			var t2 := 
	// 				s.request_queue; 				
	// 			(t1, t2); 		
	// 	s' := 
	// 		s.(election_state := t1, current_state := t2.0, request_queue := t2.1); 		
	// 	// t3
	// }

  method CProposerResetViewTimerDueToExecution(s: CProposer, val: CRequestBatch, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer) 
		requires CProposerIsValid(s)
		requires CRequestBatchIsValid(val)

    /** Manually Added for I1 */
		requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

    ensures CProposerIsValid(s') && LProposerResetViewTimerDueToExecution(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCRequestBatchToRequestBatch(val))
	{
		var t1 := 
			CElectionStateReflectExecutedRequestBatch_I1(s.election_state, val, cur_req_set, prev_req_set); /** Invoke I1 here */
		s' := 
			s.(election_state := t1); 		
		// t2
	}

/************************** AutoMan Translation End ************************/

/************************** Manual Code For I0 ************************/

/** 2 lines of manual code for I1 */
// method CProposerNominateOldValueAndSend2a(s:CProposer,log_truncation_point:COperationNumber) returns (s':CProposer, sent_packets:OutboundPackets)
// requires CProposerIsValid(s)
// requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
// requires !CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)

// /** Manually Added for I1 */
// ensures s'.election_state.cur_req_set == s.election_state.cur_req_set
// ensures s'.election_state.prev_req_set == s.election_state.prev_req_set

// ensures CProposerIsValid(s')
// ensures OutboundPacketsIsValid(sent_packets)
// ensures  LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(s), 
//                                             AbstractifyCProposerToLProposer(s'), 
//                                             AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
//                                             AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
// {
//   var opn := s.next_operation_number_to_propose;
//   if (exists p :: p in s.received_1b_packets && opn in p.msg.votes
//                   && CValIsHighestNumberedProposal(p.msg.votes[opn].max_val, s.received_1b_packets, opn))
//   {
    
//     var p :| p in s.received_1b_packets && opn in p.msg.votes
//                   && CValIsHighestNumberedProposal(p.msg.votes[opn].max_val, s.received_1b_packets, opn);
//     assert CValIsHighestNumberedProposal(p.msg.votes[opn].max_val, s.received_1b_packets, opn);
//     assert LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(p.msg.votes[opn].max_val), 
//                                         AbstractifySet(s.received_1b_packets, AbstractifyCPacketToRslPacket),
//                                         AbstractifyCOperationNumberToOperationNumber(opn));

//     s' := s.(next_operation_number_to_propose := s.next_operation_number_to_propose + 1);
//     sent_packets := Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2a(s.max_ballot_i_sent_1a, opn, p.msg.votes[opn].max_val)));
//     assert LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(s), 
//                                             AbstractifyCProposerToLProposer(s'), 
//                                             AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
//                                             AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
//   } else {
//     /** This is a branch that cannot be executed, so we use an axiom lemma to pass the verification */
//     s' := s;
//     sent_packets := Broadcast(CBroadcastNop);
//     lemma_CProposerNominateOldValueAndSend2a(s,log_truncation_point,s',sent_packets);
//     assert LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(s), 
//                                             AbstractifyCProposerToLProposer(s'), 
//                                             AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
//                                             AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
//   }
// }

// lemma {:axiom} lemma_CProposerNominateOldValueAndSend2a(s:CProposer,log_truncation_point:COperationNumber, s':CProposer, sent_packets:OutboundPackets)
//   requires CProposerIsValid(s)
//   requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
//   requires !CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
//   ensures CProposerIsValid(s')
//   ensures OutboundPacketsIsValid(sent_packets)
//   ensures  LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(s), 
//                                               AbstractifyCProposerToLProposer(s'), 
//                                               AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
//                                               AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))

/** 2 lines manual code for I1 */
// method CProposerMaybeNominateValueAndSend2a(proposer:CProposer, clock:int, log_truncation_point:COperationNumber) returns (proposer':CProposer, sent_packets:OutboundPackets)
//   requires CProposerIsValid(proposer)
//   ensures CProposerIsValid(proposer')
//   ensures OutboundPacketsIsValid(sent_packets)

//   /** Manually Added for I1 */
//   ensures proposer'.election_state.cur_req_set == proposer.election_state.cur_req_set
//   ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set

//   ensures  LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer),
//                                                 AbstractifyCProposerToLProposer(proposer'),
//                                                 clock as int,
//                                                 AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
//                                                 AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
// {
//   if !CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point, proposer.next_operation_number_to_propose) {
//     proposer' := proposer;
//     sent_packets := Broadcast(CBroadcastNop);
//   } else if !CAllAcceptorsHadNoProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose) {
//     proposer', sent_packets := CProposerNominateOldValueAndSend2a(proposer, log_truncation_point);
//   }
//   else if
//     CExistsAcceptorHasProposalLargeThanOpn(proposer.received_1b_packets, proposer.next_operation_number_to_propose)
//     || (|proposer.request_queue| >= proposer.constants.all.params.max_batch_size as int)
//     || (|proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= proposer.incomplete_batch_timer.when)
//   {
//     var (proposer'_, sent_packets_) := CProposerNominateNewValueAndSend2a(proposer, clock, log_truncation_point);
//     proposer' := proposer'_;
//     sent_packets := sent_packets_;
//   } else if |proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOff? {
//     proposer' := proposer.(incomplete_batch_timer := CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, proposer.constants.all.params.max_batch_delay, proposer.constants.all.params.max_integer_val)));
//     sent_packets := Broadcast(CBroadcastNop);
//   } else {
//     proposer' := proposer;
//     sent_packets := Broadcast(CBroadcastNop);
//   }
// }
/************************** Manual Code For I0 End ************************/

/************************** Manually Optimization for I1 ********************/

method Proposer_CanNominateUsingOperationNumberImpl(proposer:CProposer,log_truncation_point:COperationNumber) returns (b:bool)
  requires CProposerIsValid(proposer)
  requires COperationNumberIsAbstractable(log_truncation_point)
  ensures  b == CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point,
                                                         proposer.next_operation_number_to_propose)
  ensures  b == LProposerCanNominateUsingOperationNumber(AbstractifyCProposerToLProposer(proposer),
                                                         AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                                         AbstractifyCProposerToLProposer(proposer).next_operation_number_to_propose)
{
  if (proposer.current_state == 2) {
    var opn := proposer.next_operation_number_to_propose;
    var quorum_size := CMinQuorumSize(proposer.constants.all.config);

    var after_trunk;
    if (opn >= proposer.maxLogTruncationPoint) {
      after_trunk := true;
    } else { 
      after_trunk := CIsAfterLogTruncationPoint(opn, proposer.received_1b_packets);
    }
    var sum := UpperBoundedAdditionImpl(log_truncation_point, proposer.constants.all.params.max_log_length, proposer.constants.all.params.max_integer_val);
    assert CSetOfMessage1bAboutBallot(proposer.received_1b_packets, proposer.max_ballot_i_sent_1a);
    // lemma_Received1bBound(proposer);

    b := && proposer.election_state.current_view == proposer.max_ballot_i_sent_1a
         && proposer.current_state == 2
         && |proposer.received_1b_packets| >= quorum_size
         // Should come for free from ProposerIsValid
         //&& SetOfMessage1bAboutBallot(proposer.received_1b_packets, proposer.max_ballot_i_sent_1a)
         && after_trunk
         && opn < sum
         && opn >=0;

    assert b == CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point,
                                                         proposer.next_operation_number_to_propose);
    // if b {
    //   lemma_ProposerCanNominateUsingOperationNumberAbstractifies(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
    // } else {
    //   lemma_NotProposerCanNominateUsingOperationNumberAbstractifies(proposer, log_truncation_point, COperationNumber(proposer.next_operation_number_to_propose));
    // }
  } else {
    b := false;
  }
}

method {:timeLimitMultiplier 6} AllAcceptorsHadNoProposalImpl(proposer:CProposer) returns (b:bool)
  requires CProposerIsValid(proposer)
  requires proposer.current_state == 2
  ensures  LSetOfMessage1b(AbstractifyCProposerToLProposer(proposer).received_1b_packets)
  ensures  b == CAllAcceptorsHadNoProposal(proposer.received_1b_packets,
                                          proposer.next_operation_number_to_propose)
  ensures  b == LAllAcceptorsHadNoProposal(AbstractifyCProposerToLProposer(proposer).received_1b_packets,
                                           AbstractifyCProposerToLProposer(proposer).next_operation_number_to_propose)
{
  // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  // reveal AbstractifyCVotesToVotes();
  lemma_AbstractifyCPacketToRslPacket_isInjective();
  // lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();
  assert forall p :: p in proposer.received_1b_packets ==> CPacketIsInjectiveType(p);

  var start_time := Time.GetDebugTimeTicks();
    
  var end_time; 
    
  if(proposer.next_operation_number_to_propose < proposer.maxOpnWithProposal 
      // || proposer.maxOpnWithProposal.n == 0xffff_ffff_ffff_ffff
      ) {
    var opn := proposer.next_operation_number_to_propose;
    b := (forall p :: p in proposer.received_1b_packets ==> !(opn in p.msg.votes));
    end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("AllAcceptorsHadNoProposalImpl_full", start_time, end_time);
    //print("AllAcceptorsHadNoProposalImpl_full: Doing full search, nextOpnToPropose = ", proposer.next_operation_number_to_propose, " and maxOpnWithProposal = ", proposer.maxOpnWithProposal.n, "\n"); 
  } else {
    b := true;
    end_time := Time.GetDebugTimeTicks();
    RecordTimingSeq("AllAcceptorsHadNoProposalImpl_memoized", start_time, end_time);
    //print("AllAcceptorsHadNoProposalImpl_memoized: Memoized, nextOpnToPropose = ", proposer.next_operation_number_to_propose, " and maxOpnWithProposal = ", proposer.maxOpnWithProposal.n, "\n"); 
  }
  // lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
}


method DidSomeAcceptorHaveProposal(proposer:CProposer) returns (b:bool) //, opn:COperationNumber)
  requires CProposerIsValid(proposer)
  requires proposer.current_state == 2
  ensures  LSetOfMessage1b(AbstractifyCProposerToLProposer(proposer).received_1b_packets)
  // ensures b == (exists opn:COperationNumber ::
  //                                  opn > proposer.next_operation_number_to_propose &&
  //                                  !CAllAcceptorsHadNoProposal(proposer.received_1b_packets, opn))
  ensures b == var ref_proposer := AbstractifyCProposerToLProposer(proposer);
                   (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn))
  ensures b == var ref_proposer := AbstractifyCProposerToLProposer(proposer);
                   LExistsAcceptorHasProposalLargeThanOpn(ref_proposer.received_1b_packets, ref_proposer.next_operation_number_to_propose)
{
  // reveal AbstractifyCVotesToVotes();
  lemma_AbstractifyCPacketToRslPacket_isInjective();
  // lemma_AbstractifyCOperationNumberToOperationNumber_isInjective();
  // lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(proposer.received_1b_packets);
  assert forall p :: p in proposer.received_1b_packets ==> CPacketIsInjectiveType(p);

  if proposer.next_operation_number_to_propose >= proposer.maxOpnWithProposal {
    b := false;
  } else {
    b := (exists p :: p in proposer.received_1b_packets &&
                (exists opn:COperationNumber :: opn in p.msg.votes && opn > proposer.next_operation_number_to_propose));
  }
  // The "exists opn" needs a trigger that relates to "opn.n > ...":
  ghost var gt := (i:int, j:int) => i > j;
  assert b <==>
        (exists p :: p in proposer.received_1b_packets &&
            (exists opn:COperationNumber :: opn in p.msg.votes && gt(AbstractifyCOperationNumberToOperationNumber(opn), proposer.next_operation_number_to_propose as int)));

  ghost var ref_proposer := AbstractifyCProposerToLProposer(proposer);
  if ((exists opn :: gt(opn, ref_proposer.next_operation_number_to_propose) &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn))) {
    var ref_opn :| gt(ref_opn, ref_proposer.next_operation_number_to_propose) &&
                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, ref_opn);
    var ref_p :| ref_p in ref_proposer.received_1b_packets && ref_opn in ref_p.msg.votes;

    forall ensures exists p :: p in proposer.received_1b_packets && ref_p == AbstractifyCPacketToRslPacket(p)
    {
      // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
    }

    var p :| p in proposer.received_1b_packets && ref_p == AbstractifyCPacketToRslPacket(p);

    //assert exists o :: o in p.msg.votes.v && AbstractifyCOperationNumberToOperationNumber(o) == ref_opn;

    assert b;
  }

  assert b <==> (exists opn :: gt(opn, ref_proposer.next_operation_number_to_propose) && !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
}

predicate ExistsPred(proposer:CProposer, ref_proposer:LProposer, existsOpn:bool)
  requires CProposerIsValid(proposer)
  requires ref_proposer == AbstractifyCProposerToLProposer(proposer)
  requires LSetOfMessage1b(ref_proposer.received_1b_packets)
  requires CProposerIsValid(proposer)
{
  existsOpn <==> (exists opn :: && opn > ref_proposer.next_operation_number_to_propose 
                         && LSetOfMessage1b(ref_proposer.received_1b_packets)
                         && !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn))
}

lemma {:axiom} lemma_DidSomeAcceptorHaveProposal(proposer:CProposer) //, opn:COperationNumber)
  requires CProposerIsValid(proposer)
  requires proposer.current_state == 2
  requires proposer.next_operation_number_to_propose >= proposer.maxOpnWithProposal
  ensures  LSetOfMessage1b(AbstractifyCProposerToLProposer(proposer).received_1b_packets)
  ensures !(exists opn:COperationNumber ::
                                   opn > proposer.next_operation_number_to_propose &&
                                   !CAllAcceptorsHadNoProposal(proposer.received_1b_packets, opn))
  ensures !var ref_proposer := AbstractifyCProposerToLProposer(proposer);
                   (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn))


lemma {:axiom} lemma_AllAcceptorsHadNoProposalImpl(proposer:CProposer)
  requires CProposerIsValid(proposer)
  requires proposer.current_state == 2
  // requires proposer.maxOpnWithProposal.n < 0xffff_ffff_ffff_ffff
  requires proposer.next_operation_number_to_propose >= proposer.maxOpnWithProposal
  ensures  LSetOfMessage1b(AbstractifyCProposerToLProposer(proposer).received_1b_packets)
  ensures  CAllAcceptorsHadNoProposal(proposer.received_1b_packets,
                                     proposer.next_operation_number_to_propose)
  ensures  LAllAcceptorsHadNoProposal(AbstractifyCProposerToLProposer(proposer).received_1b_packets,
                                      AbstractifyCProposerToLProposer(proposer).next_operation_number_to_propose)

method {:timeLimitMultiplier 12} CProposerMaybeNominateValueAndSend2a(proposer:CProposer, clock:int, log_truncation_point:COperationNumber) 
  returns (proposer':CProposer, sent_packets:OutboundPackets)
  requires CProposerIsValid(proposer)
  requires COperationNumberIsAbstractable(log_truncation_point)
  ensures  CProposerIsValid(proposer')
  ensures  OutboundPacketsIsValid(sent_packets)
  ensures  OutboundPacketsHasCorrectSrc(sent_packets, proposer.constants.all.config.replica_ids[proposer.constants.my_index])
  ensures  LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer), AbstractifyCProposerToLProposer(proposer'), clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
  ensures proposer.constants == proposer'.constants
  ensures proposer'.election_state.cur_req_set == proposer.election_state.cur_req_set
  ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set
{
  //var start_time := Time.GetDebugTimeTicks();
  var canNominate := Proposer_CanNominateUsingOperationNumberImpl(proposer, log_truncation_point);
  //var end_time:= Time.GetDebugTimeTicks();
  //RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_preamble_Proposer_CanNominateUsingOperationNumberImpl", start_time, end_time);
  /*
  //start_time := Time.GetDebugTimeTicks();
    
  end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_preamble_AllAcceptorsHadNoProposalImpl", start_time, end_time);

  //start_time := Time.GetDebugTimeTicks();
    
  end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_preamble", start_time, end_time);
  */
  //print("ProposerMaybeNominateValueAndSend2a: proposer.next_operation_number_to_propose = ", proposer.next_operation_number_to_propose, ", canNominate = ", canNominate, "\n");
    
  if !canNominate {
    proposer' := proposer;
    sent_packets := Broadcast(CBroadcastNop);
    assert LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer), AbstractifyCProposerToLProposer(proposer'), clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  } else {
    if (proposer.next_operation_number_to_propose >= proposer.maxOpnWithProposal && |proposer.request_queue| == 0) {
      lemma_DidSomeAcceptorHaveProposal(proposer);
      lemma_AllAcceptorsHadNoProposalImpl(proposer);
            
      //start_time := Time.GetDebugTimeTicks();
      proposer' := proposer;
      sent_packets := Broadcast(CBroadcastNop);
      assert LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer), AbstractifyCProposerToLProposer(proposer'), clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
    } else {
      var noProposal := AllAcceptorsHadNoProposalImpl(proposer);
      //var end_time2 := Time.GetDebugTimeTicks();
      //RecordTimingSeq("ProposerMaybeNominateValueAndSend2a_AllAcceptorsHadNoProposalImpl", start_time, end_time2);
      //print("ProposerMaybeNominateValueAndSend2a: proposer.next_operation_number_to_propose = ", proposer.next_operation_number_to_propose, ", AllAcceptorsHadNoProposalImpl = ", noProposal, "\n");
      if !noProposal {
        // newproposer, sent := CProposerNominateOldValueAndSend2a(proposer, log_truncation_point);
        proposer', sent_packets := CProposerNominateOldValueAndSend2a(proposer, log_truncation_point);
        assert LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer), AbstractifyCProposerToLProposer(proposer'), clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
      } else {
        var queueSize := |proposer.request_queue|;
        var existsOpn := DidSomeAcceptorHaveProposal(proposer);
        ghost var ref_proposer := AbstractifyCProposerToLProposer(proposer);
        assert existsOpn ==> (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
        assert ExistsPred(proposer, ref_proposer, existsOpn);
        //var end_time3 := Time.GetDebugTimeTicks();
        //var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
        //   (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
        //                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
        if existsOpn {
          assert ExistsPred(proposer, ref_proposer, existsOpn);
          assert existsOpn ==> (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
          assert exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn);
          //ghost var opn :| opn > ref_proposer.next_operation_number_to_propose &&
          //               !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn);
        } else {
           assert forall opn :: !(opn > ref_proposer.next_operation_number_to_propose &&
                                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
        }
        //assert existsOpn <==> var ref_proposer := AbstractifyProposerStateToLProposer(proposer);(exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
        //                   !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));

        //                  ;var ref_proposer := AbstractifyProposerStateToLProposer(proposer);
        //  (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
        //                  !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));

        if (|| (queueSize > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= proposer.incomplete_batch_timer.when)
            || (queueSize >= proposer.constants.all.params.max_batch_size)
            || existsOpn) {
          if existsOpn {
            assert ExistsPred(proposer, ref_proposer, existsOpn);
            assert existsOpn ==> (exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                       !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn));
            assert exists opn :: opn > ref_proposer.next_operation_number_to_propose &&
                                       !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn);
            //ghost var opn :| opn > ref_proposer.next_operation_number_to_propose &&
            //               !LAllAcceptorsHadNoProposal(ref_proposer.received_1b_packets, opn);
          } else if (queueSize >= proposer.constants.all.params.max_batch_size as int) {
            assert |ref_proposer.request_queue| >= ref_proposer.constants.all.params.max_batch_size;
          } else if (queueSize > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= proposer.incomplete_batch_timer.when) {
            assert (|ref_proposer.request_queue| > 0 && ref_proposer.incomplete_batch_timer.IncompleteBatchTimerOn? && clock as int >= ref_proposer.incomplete_batch_timer.when);
          }
          //assert existsOpn <==> 
          //    (exists opn:OperationNumber :: 
          //        (opn > AbstractifyProposerStateToLProposer(proposer).next_operation_number_to_propose 
          //     && !LAllAcceptorsHadNoProposal(AbstractifyProposerStateToLProposer(proposer).received_1b_packets, opn))
          //     );
          // var sent:OutboundPackets;
  // print "I am leader\n";
          var (newproposer, sent) := CProposerNominateNewValueAndSend2a(proposer, clock, log_truncation_point);
          // proposer', sent := CProposerNominateNewValueAndSend2a(proposer, clock, log_truncation_point);
          assert LProposerNominateNewValueAndSend2a(
              AbstractifyCProposerToLProposer(proposer), 
              AbstractifyCProposerToLProposer(newproposer), 
              clock, 
              AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
              AbstractifyOutboundCPacketsToSeqOfRslPackets(sent));
          proposer' := newproposer;
          assert sent.Broadcast?;
          sent_packets := sent;
          assert OutboundPacketsHasCorrectSrc(sent, proposer.constants.all.config.replica_ids[proposer.constants.my_index]); //OBSERVE

          assert LProposerNominateNewValueAndSend2a(
              AbstractifyCProposerToLProposer(proposer), 
              AbstractifyCProposerToLProposer(proposer'), 
              clock, 
              AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
              AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
          assert LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer), AbstractifyCProposerToLProposer(proposer'), clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
        } else {
          if ( queueSize > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOff? ) {
            var sum := UpperBoundedAdditionImpl(clock, proposer.constants.all.params.max_batch_delay, proposer.constants.all.params.max_integer_val);
            proposer' := proposer.(incomplete_batch_timer := CIncompleteBatchTimerOn(sum));
            sent_packets := Broadcast(CBroadcastNop);
            assert LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer), AbstractifyCProposerToLProposer(proposer'), clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
          } else {
            proposer' := proposer;
            sent_packets := Broadcast(CBroadcastNop);
            assert LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer), AbstractifyCProposerToLProposer(proposer'), clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
          }
        }
      }
    }
  }
}

// lemma {:axiom} lemma_CProposerValid(s:CProposer)
//   ensures CProposerIsValid(s)
// lemma {:axiom} lemma_FindValWithHighestNumberedProposal(received_1b_packets:set<CPacket>, opn:COperationNumber, v:CRequestBatch)
//   requires received_1b_packets != {}
//   requires COperationNumberIsAbstractable(opn)
//   requires CSetOfMessage1b(received_1b_packets)
//   requires CPacketsIsAbstractable(received_1b_packets)
//   requires (forall i :: i in received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
//   requires SetIsInjective(received_1b_packets, AbstractifyCPacketToRslPacket)
//   requires !CAllAcceptorsHadNoProposal(received_1b_packets, opn)
//   requires forall p :: p in received_1b_packets ==> CVotesIsValid(p.msg.votes)
//   ensures CRequestBatchIsAbstractable(v)
//   ensures CRequestBatchIsValid(v)
//   ensures LSetOfMessage1b(AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket))
//   ensures LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn))
//   ensures CValIsHighestNumberedProposal(v, received_1b_packets, opn)

 
method {:timeLimitMultiplier 5} FindValWithHighestNumberedProposal(received_1b_packets:set<CPacket>, opn:COperationNumber) returns (v:CRequestBatch)
  requires received_1b_packets != {}
  requires COperationNumberIsAbstractable(opn)
  requires CSetOfMessage1b(received_1b_packets)
  requires CPacketsIsAbstractable(received_1b_packets)
  requires (forall i :: i in received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
  requires SetIsInjective(received_1b_packets, AbstractifyCPacketToRslPacket)
  requires !CAllAcceptorsHadNoProposal(received_1b_packets, opn)
  requires forall p :: p in received_1b_packets ==> CVotesIsValid(p.msg.votes)
  ensures CRequestBatchIsAbstractable(v)
  ensures CRequestBatchIsValid(v)
  ensures LSetOfMessage1b(AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket))
  ensures LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn))
  ensures CValIsHighestNumberedProposal(v, received_1b_packets, opn)
{
  var packets:set<CPacket>;
  ghost var processedPackets:set<CPacket>;

  packets := received_1b_packets;
  var pkt :| pkt in packets && opn in pkt.msg.votes;
  v := pkt.msg.votes[opn].max_val;
  var bal := pkt.msg.votes[opn].max_value_bal;
  var p_bal := pkt;
  packets := packets - {pkt};
  processedPackets := {pkt};
  // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  // reveal AbstractifyCVotesToVotes();
  ghost var p := AbstractifyCPacketToRslPacket(pkt);
  ghost var S := AbstractifySet(processedPackets, AbstractifyCPacketToRslPacket);
  ghost var opn_s := AbstractifyCOperationNumberToOperationNumber(opn);

  while (packets != {})
    decreases packets
    invariant packets + processedPackets == received_1b_packets
    invariant processedPackets == received_1b_packets - packets
    invariant CRequestBatchIsAbstractable(v) && CBallotIsAbstractable(bal) && CPacketIsAbstractable(p_bal) && p_bal in processedPackets && opn in p_bal.msg.votes && v == p_bal.msg.votes[opn].max_val && bal == p_bal.msg.votes[opn].max_value_bal
    invariant forall q :: q in processedPackets && opn in q.msg.votes ==> CBalLeq(q.msg.votes[opn].max_value_bal, p_bal.msg.votes[opn].max_value_bal)
    invariant p_bal in processedPackets
    invariant opn in p_bal.msg.votes
    invariant p_bal.msg.votes[opn].max_value_bal==bal
    invariant p_bal.msg.votes[opn].max_val==v
    invariant CExistsBallotInS(v, bal, processedPackets, opn)
    invariant CValIsHighestNumberedProposalAtBallot(v, bal, processedPackets, opn)
    invariant CValIsHighestNumberedProposal(v, processedPackets, opn)
    invariant CRequestBatchIsValid(v)
  {
    pkt :| pkt in packets;
    if (opn in pkt.msg.votes) {
      var foundHigherBallot := CBalLeq(bal, pkt.msg.votes[opn].max_value_bal);

      if (foundHigherBallot) {
        p_bal := pkt;
        v := pkt.msg.votes[opn].max_val;
        bal := pkt.msg.votes[opn].max_value_bal;
      }
    }
    packets := packets - {pkt};
    processedPackets := processedPackets + {pkt};
    // reveal AbstractifyCVotesToVotes();
  }
  lemma_FindValWithHighestNumberedProposal(received_1b_packets, opn, v);
  // assert processedPackets == received_1b_packets;
  // p := AbstractifyCPacketToRslPacket(p_bal);
  // assert CValIsHighestNumberedProposal(v, received_1b_packets, opn);
  // lemma_CValIsHighestNumberedProposalAbstractifies(v, bal, received_1b_packets, opn);
  // assert LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn));
}

// method {:timeLimitMultiplier 5} FindValWithHighestNumberedProposal(received_1b_packets:set<CPacket>, opn:COperationNumber) returns (v:CRequestBatch)
//   requires received_1b_packets != {}
//   requires COperationNumberIsAbstractable(opn)
//   requires CSetOfMessage1b(received_1b_packets)
//   requires CPacketsIsAbstractable(received_1b_packets)
//   requires (forall i :: i in received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
//   requires SetIsInjective(received_1b_packets, AbstractifyCPacketToRslPacket)
//   requires !CAllAcceptorsHadNoProposal(received_1b_packets, opn)
//   requires forall p :: p in received_1b_packets ==> CVotesIsValid(p.msg.votes)
//   ensures CRequestBatchIsAbstractable(v)
//   ensures CRequestBatchIsValid(v)
//   ensures LSetOfMessage1b(AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket))
//   ensures LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn))
//   ensures CValIsHighestNumberedProposal(v, received_1b_packets, opn)
// {
//   var packets:set<CPacket>;
//   ghost var processedPackets:set<CPacket>;

//   packets := received_1b_packets;
//   var pkt :| pkt in packets && opn in pkt.msg.votes;
//   v := pkt.msg.votes[opn].max_val;
//   var bal := pkt.msg.votes[opn].max_value_bal;
//   var p_bal := pkt;
//   packets := packets - {pkt};
//   processedPackets := {pkt};
//   // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
//   // reveal AbstractifyCVotesToVotes();
//   ghost var p := AbstractifyCPacketToRslPacket(pkt);
//   ghost var S := AbstractifySet(processedPackets, AbstractifyCPacketToRslPacket);
//   ghost var opn_s := AbstractifyCOperationNumberToOperationNumber(opn);

//   while (packets != {})
//     decreases packets
//     invariant packets + processedPackets == received_1b_packets
//     invariant processedPackets == received_1b_packets - packets
//     invariant CRequestBatchIsAbstractable(v) && CBallotIsAbstractable(bal) && CPacketIsAbstractable(p_bal) && p_bal in processedPackets && opn in p_bal.msg.votes && v == p_bal.msg.votes[opn].max_val && bal == p_bal.msg.votes[opn].max_value_bal
//     invariant forall q :: q in processedPackets && opn in q.msg.votes ==> CBalLeq(q.msg.votes[opn].max_value_bal, p_bal.msg.votes[opn].max_value_bal)
//     invariant p_bal in processedPackets
//     invariant opn in p_bal.msg.votes
//     invariant p_bal.msg.votes[opn].max_value_bal==bal
//     invariant p_bal.msg.votes[opn].max_val==v
//     invariant CExistsBallotInS(v, bal, processedPackets, opn)
//     invariant CValIsHighestNumberedProposalAtBallot(v, bal, processedPackets, opn)
//     invariant CValIsHighestNumberedProposal(v, processedPackets, opn)
//     invariant CRequestBatchIsValid(v)
//   {
//     pkt :| pkt in packets;
//     if (opn in pkt.msg.votes) {
//       var foundHigherBallot := CBalLeq(bal, pkt.msg.votes[opn].max_value_bal);

//       if (foundHigherBallot) {
//         p_bal := pkt;
//         v := pkt.msg.votes[opn].max_val;
//         bal := pkt.msg.votes[opn].max_value_bal;
//       }
//     }
//     packets := packets - {pkt};
//     processedPackets := processedPackets + {pkt};
//     // reveal AbstractifyCVotesToVotes();
//   }

//   assert processedPackets == received_1b_packets;
//   p := AbstractifyCPacketToRslPacket(p_bal);
//   assert CValIsHighestNumberedProposal(v, received_1b_packets, opn);
//   lemma_CValIsHighestNumberedProposalAbstractifies(v, bal, received_1b_packets, opn);
//   assert LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn));
// }


lemma lemma_CValIsHighestNumberedProposalAbstractifies(v:CRequestBatch, bal:CBallot, S:set<CPacket>, opn:COperationNumber)
  requires CRequestBatchIsAbstractable(v) && CBallotIsAbstractable(bal) && CPacketsIsAbstractable(S) && COperationNumberIsAbstractable(opn)
  requires CSetOfMessage1b(S)
  requires CRequestBatchIsValid(v)
  requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
  requires COperationNumberIsValid(opn)
  requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
  requires CValIsHighestNumberedProposal(v, S, opn)
  requires CValIsHighestNumberedProposalAtBallot(v, bal, S, opn)
  ensures LSetOfMessage1b(AbstractifySet(S, AbstractifyCPacketToRslPacket))
  ensures LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn))
  ensures LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn))
{
  // reveal AbstractifyCVotesToVotes();

  var c :| CBallotIsAbstractable(c) && CValIsHighestNumberedProposalAtBallot(v, c, S, opn);
  var ref_c := AbstractifyCBallotToBallot(c);
  var ref_v := AbstractifyCRequestBatchToRequestBatch(v);
  var ref_S := AbstractifySet(S, AbstractifyCPacketToRslPacket);
  var ref_opn := AbstractifyCOperationNumberToOperationNumber(opn);
  // forall ensures LMaxBallotInS(ref_c, ref_S, ref_opn)
  // {
  //   lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(S);
  // }
  // lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(S);
  assert Lmax_balInS(ref_c, ref_S, ref_opn);
  assert CExistsBallotInS(v, c, S, opn);
  var p :| && p in S
           && opn in p.msg.votes
           && p.msg.votes[opn].max_value_bal==c
           && p.msg.votes[opn].max_val==v;
  var ref_p := AbstractifyCPacketToRslPacket(p);

  forall ensures ref_p in ref_S
  {
    // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  }
  assert ref_opn in ref_p.msg.votes;
  assert ref_p.msg.votes[ref_opn].max_value_bal == ref_c;
  assert ref_p.msg.votes[ref_opn].max_val == ref_v;

  assert LExistsBallotInS(ref_v, ref_c, ref_S, ref_opn);
  assert LValIsHighestNumberedProposalAtBallot(ref_v, ref_c, ref_S, ref_opn);
  assert LValIsHighestNumberedProposal(ref_v, ref_S, ref_opn);

  var ref_bal := AbstractifyCBallotToBallot(bal);
  assert CExistsBallotInS(v, bal, S, opn);

  var p' :| && p' in S
            && opn in p'.msg.votes
            && p'.msg.votes[opn].max_value_bal==bal
            && p'.msg.votes[opn].max_val==v;

  assert AbstractifyCRequestBatchToRequestBatch(p'.msg.votes[opn].max_val) == AbstractifyCRequestBatchToRequestBatch(v);

  var ref_p' := AbstractifyCPacketToRslPacket(p');

  forall ensures ref_p' in ref_S
  {
    // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  }

  assert ref_opn in ref_p'.msg.votes;
  assert ref_p'.msg.votes[ref_opn].max_value_bal == ref_bal;
  assert ref_p'.msg.votes[ref_opn].max_val == ref_v;
  assert LExistsBallotInS(ref_v, ref_bal, ref_S, ref_opn);

  assert LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn));
}


method CProposerNominateOldValueAndSend2a(proposer:CProposer,log_truncation_point:COperationNumber) returns (proposer':CProposer, sent_packets:OutboundPackets)
    requires CProposerIsValid(proposer)
    requires CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point, proposer.next_operation_number_to_propose)
    requires !CAllAcceptorsHadNoProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose)
    ensures CProposerIsValid(proposer')
    ensures OutboundPacketsIsValid(sent_packets)
    ensures LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(proposer),
                                               AbstractifyCProposerToLProposer(proposer'),
                                               AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                               AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
    ensures proposer.election_state == proposer'.election_state
  {
    var opn := proposer.next_operation_number_to_propose;
    var v := FindValWithHighestNumberedProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose);

    proposer' := proposer.(next_operation_number_to_propose := proposer.next_operation_number_to_propose + 1);
    var cmsg := CMessage_2a(proposer.max_ballot_i_sent_1a, opn, v);
    sent_packets := Broadcast(BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, cmsg));
  }
/************************** Manually Optimization for I1 End ********************/

  lemma {:axiom} lemma_RequestQueue_len(s:seq<CRequest>)
    ensures |s| <= RequestBatchSizeLimit()
}
