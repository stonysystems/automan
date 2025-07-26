include "../../Protocol/ByzRSL/Message.i.dfy"
include "../../Protocol/ByzRSL/Environment.i.dfy"
include "../../Protocol/ByzRSL/Broadcast.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "CTypes.i.dfy"

module LiveByzRSL__CMessage_i {
  import opened LiveByzRSL__CTypes_i
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__AppInterface_i
  import opened Logic__Option_i
  import opened LiveByzRSL__Message_i
  import opened GenericRefinement_i
  import opened LiveByzRSL__Environment_i
  import opened Common__NodeIdentity_i
  import opened Common__UdpClient_i
  import opened Environment_s
  import opened Concrete_NodeIdentity_i

/************************** AutoMan Translation ************************/
/** 65 + 0 */
datatype CMessage = 
	CMessage_Invalid(
		
	)
	 | 
	CMessage_Request(
		seqno_req: int, 
		val: CAppMessage
	)
	 | 
	CMessage_1a(
		bal_1a: CBallot
	)
	 | 
	CMessage_1b(
		bal_1b: CBallot, 
		log_truncation_point: COperationNumber, 
		votes: CVotes
	)
	 | 
	CMessage_1c(
		bal_1c: CBallot, 
		opn_1c: COperationNumber, 
		val_1c: CRequestBatch
	)
	 | 
	CMessage_2av(
		bal_2av: CBallot, 
		opn_2av: COperationNumber, 
		val_2av: CRequestBatch
	)
	 | 
	CMessage_2b(
		bal_2b: CBallot, 
		opn_2b: COperationNumber, 
		val_2b: CRequestBatch
	)
	 | 
	CMessage_Heartbeat(
		bal_heartbeat: CBallot, 
		suspicious: bool, 
		opn_ckpt: COperationNumber
	)
	 | 
	CMessage_Reply(
		seqno_reply: int, 
		reply: CAppMessage
	)
	//  | 
	// CMessage_AppStateRequest(
	// 	bal_state_req: CBallot, 
	// 	opn_state_req: COperationNumber
	// )
	//  | 
	// CMessage_AppStateSupply(
	// 	bal_state_supply: CBallot, 
	// 	opn_state_supply: COperationNumber, 
	// 	app_state: CAppState, 
	// 	reply_cache: CReplyCache
	// )
	 | 
	CMessage_StartingPhase2(
		bal_2: CBallot, 
		logTruncationPoint_2: COperationNumber
	)


  /** 0 + 16 */
	predicate CMessageIsValid(s: CMessage) 
	{
		match s
		case CMessage_Invalid() => CMessageIsAbstractable(s)
		case CMessage_Request(seqno_req, val) => CMessageIsAbstractable(s) && CAppMessageIsValid(s.val)
		case CMessage_1a(bal_1a) => CMessageIsAbstractable(s) && CBallotIsValid(s.bal_1a)
		case CMessage_1b(bal_1b, log_truncation_point, votes) => CMessageIsAbstractable(s) && CBallotIsValid(s.bal_1b) && COperationNumberIsValid(s.log_truncation_point) && CVotesIsValid(s.votes)
		case CMessage_1c(bal_1c, opn_1c, val_1c) => CMessageIsAbstractable(s) && CBallotIsValid(s.bal_1c) && COperationNumberIsValid(s.opn_1c) && CRequestBatchIsValid(s.val_1c)
		case CMessage_2av(bal_2av, opn_2av, val_2av) => CMessageIsAbstractable(s) && CBallotIsValid(bal_2av) && COperationNumberIsValid(opn_2av) && CRequestBatchIsValid(val_2av)
		case CMessage_2b(bal_2b, opn_2b, val_2b) => CMessageIsAbstractable(s) && CBallotIsValid(s.bal_2b) && COperationNumberIsValid(s.opn_2b) && CRequestBatchIsValid(s.val_2b)
		case CMessage_Heartbeat(bal_heartbeat, suspicious, opn_ckpt) => CMessageIsAbstractable(s) && CBallotIsValid(s.bal_heartbeat) && COperationNumberIsValid(s.opn_ckpt)
		case CMessage_Reply(seqno_reply, reply) => CMessageIsAbstractable(s) && CAppMessageIsValid(s.reply)
		// case CMessage_AppStateRequest(bal_state_req, opn_state_req) => CMessageIsAbstractable(s) && CBallotIsValid(s.bal_state_req) && COperationNumberIsValid(s.opn_state_req)
		// case CMessage_AppStateSupply(bal_state_supply, opn_state_supply, app_state, reply_cache) => CMessageIsAbstractable(s) && CBallotIsValid(s.bal_state_supply) && COperationNumberIsValid(s.opn_state_supply) && CAppStateIsValid(s.app_state) && CReplyCacheIsValid(s.reply_cache)
		case CMessage_StartingPhase2(bal_2, logTruncationPoint_2) => CMessageIsAbstractable(s) && CBallotIsValid(s.bal_2) && COperationNumberIsValid(s.logTruncationPoint_2)

	}

  /** 0 + 16 */
	predicate CMessageIsAbstractable(s: CMessage) 
	{
		match s
		case CMessage_Invalid() => true
		case CMessage_Request(seqno_req, val) => CAppMessageIsAbstractable(s.val)
		case CMessage_1a(bal_1a) => CBallotIsAbstractable(s.bal_1a)
		case CMessage_1b(bal_1b, log_truncation_point, votes) => CBallotIsAbstractable(s.bal_1b) && COperationNumberIsAbstractable(s.log_truncation_point) && CVotesIsAbstractable(s.votes)
		case CMessage_1c(bal_1c, opn_1c, val_1c) => CBallotIsAbstractable(s.bal_1c) && COperationNumberIsAbstractable(s.opn_1c) && CRequestBatchIsAbstractable(s.val_1c)
		case CMessage_2av(bal_2av, opn_2av, val_2av) => CBallotIsAbstractable(s.bal_2av) && COperationNumberIsAbstractable(s.opn_2av) && CRequestBatchIsAbstractable(s.val_2av)
		case CMessage_2b(bal_2b, opn_2b, val_2b) => CBallotIsAbstractable(s.bal_2b) && COperationNumberIsAbstractable(s.opn_2b) && CRequestBatchIsAbstractable(s.val_2b)
		case CMessage_Heartbeat(bal_heartbeat, suspicious, opn_ckpt) => CBallotIsAbstractable(s.bal_heartbeat) && COperationNumberIsAbstractable(s.opn_ckpt)
		case CMessage_Reply(seqno_reply, reply) => CAppMessageIsAbstractable(s.reply)
		// case CMessage_AppStateRequest(bal_state_req, opn_state_req) => CBallotIsAbstractable(s.bal_state_req) && COperationNumberIsAbstractable(s.opn_state_req)
		// case CMessage_AppStateSupply(bal_state_supply, opn_state_supply, app_state, reply_cache) => CBallotIsAbstractable(s.bal_state_supply) && COperationNumberIsAbstractable(s.opn_state_supply) && CAppStateIsAbstractable(s.app_state) && CReplyCacheIsAbstractable(s.reply_cache)
		case CMessage_StartingPhase2(bal_2, logTruncationPoint_2) => CBallotIsAbstractable(s.bal_2) && COperationNumberIsAbstractable(s.logTruncationPoint_2)

	}

  /** 0 + 16 */
	function AbstractifyCMessageToRslMessage(s: CMessage) : RslMessage 
		requires CMessageIsAbstractable(s)
	{
		match s
		case CMessage_Invalid() => RslMessage_Invalid()
		case CMessage_Request(seqno_req, val) => RslMessage_Request(s.seqno_req, AbstractifyCAppMessageToAppMessage(s.val))
		case CMessage_1a(bal_1a) => RslMessage_1a(AbstractifyCBallotToBallot(s.bal_1a))
		case CMessage_1b(bal_1b, log_truncation_point, votes) => RslMessage_1b(AbstractifyCBallotToBallot(s.bal_1b), AbstractifyCOperationNumberToOperationNumber(s.log_truncation_point), AbstractifyCVotesToVotes(s.votes))
		case CMessage_1c(bal_1c, opn_1c, val_1c) => RslMessage_1c(AbstractifyCBallotToBallot(s.bal_1c), AbstractifyCOperationNumberToOperationNumber(s.opn_1c), AbstractifyCRequestBatchToRequestBatch(s.val_1c))
		case CMessage_2av(bal_2av, opn_2av, val_2av) => RslMessage_2av(AbstractifyCBallotToBallot(s.bal_2av), AbstractifyCOperationNumberToOperationNumber(s.opn_2av), AbstractifyCRequestBatchToRequestBatch(s.val_2av))
		case CMessage_2b(bal_2b, opn_2b, val_2b) => RslMessage_2b(AbstractifyCBallotToBallot(s.bal_2b), AbstractifyCOperationNumberToOperationNumber(s.opn_2b), AbstractifyCRequestBatchToRequestBatch(s.val_2b))
		case CMessage_Heartbeat(bal_heartbeat, suspicious, opn_ckpt) => RslMessage_Heartbeat(AbstractifyCBallotToBallot(s.bal_heartbeat), s.suspicious, AbstractifyCOperationNumberToOperationNumber(s.opn_ckpt))
		case CMessage_Reply(seqno_reply, reply) => RslMessage_Reply(s.seqno_reply, AbstractifyCAppMessageToAppMessage(s.reply))
		// case CMessage_AppStateRequest(bal_state_req, opn_state_req) => RslMessage_AppStateRequest(AbstractifyCBallotToBallot(s.bal_state_req), AbstractifyCOperationNumberToOperationNumber(s.opn_state_req))
		// case CMessage_AppStateSupply(bal_state_supply, opn_state_supply, app_state, reply_cache) => RslMessage_AppStateSupply(AbstractifyCBallotToBallot(s.bal_state_supply), AbstractifyCOperationNumberToOperationNumber(s.opn_state_supply), AbstractifyCAppStateToAppState(s.app_state), AbstractifyCReplyCacheToReplyCache(s.reply_cache))
		case CMessage_StartingPhase2(bal_2, logTruncationPoint_2) => RslMessage_StartingPhase2(AbstractifyCBallotToBallot(s.bal_2), AbstractifyCOperationNumberToOperationNumber(s.logTruncationPoint_2))

	}


/************************** AutoMan Translation End ************************/
  
  /* ----------------------------------------- */

  datatype CPacket = CPacket(dst:EndPoint, src:EndPoint, msg:CMessage)

  predicate CPacketIsValid(cp:CPacket)
  {
    && CPacketIsAbstractable(cp)
    && CMessageIsValid(cp.msg)
    && EndPointIsValid(cp.src)
    && EndPointIsValid(cp.dst)
  }

  predicate CPacketIsAbstractable(cp:CPacket)
  {
    && CMessageIsAbstractable(cp.msg)
    && EndPointIsAbstractable(cp.src)
    && EndPointIsAbstractable(cp.dst)
  }

  function AbstractifyCPacketToRslPacket(cp: CPacket): RslPacket
    requires CPacketIsAbstractable(cp)
  {
    LPacket(AbstractifyEndPointToNodeIdentity(cp.dst), AbstractifyEndPointToNodeIdentity(cp.src), AbstractifyCMessageToRslMessage(cp.msg))
  }


  // not exist in protocol, but seems well defined than in protocol
  datatype CBroadcast = CBroadcast(src:EndPoint, dsts:seq<EndPoint>, msg:CMessage) | CBroadcastNop

  predicate CBroadcastIsAbstractable(broadcast:CBroadcast)
  {
    match broadcast
    case CBroadcastNop => true
    case CBroadcast(src,dsts,msg) =>
      && EndPointIsAbstractable(src)
      && (forall i :: 0 <= i < |broadcast.dsts| ==> EndPointIsAbstractable(broadcast.dsts[i]))
      && CMessageIsAbstractable(broadcast.msg)
         // || (&& broadcast.CBroadcast?
         //    && EndPointIsValidIPV4(broadcast.src)
         //    && (forall i :: 0 <= i < |broadcast.dsts| ==> EndPointIsValidIPV4(broadcast.dsts[i]))
         //    && CMessageIsAbstractable(broadcast.msg))
  }

  predicate CBroadcastValid(c:CBroadcast)
  {
    && CBroadcastIsAbstractable(c)
    && match c
       case CBroadcastNop => true
       case CBroadcast(src,dsts,msg) =>
         && EndPointIsValid(src)
         && (forall i :: 0 <= i < |c.dsts| ==> EndPointIsValid(c.dsts[i]))
         && CMessageIsValid(c.msg)
  }

  function {:opaque} BuildLBroadcast(src:NodeIdentity, dsts:seq<NodeIdentity>, m:RslMessage):seq<RslPacket>
    ensures |BuildLBroadcast(src, dsts, m)| == |dsts|
    ensures forall i :: 0 <= i < |dsts| ==> BuildLBroadcast(src, dsts, m)[i] == LPacket(dsts[i], src, m)
  {
    if |dsts| == 0 then []
    else [LPacket(dsts[0], src, m)] + BuildLBroadcast(src, dsts[1..], m)
  }

  function AbstractifyCBroadcastToRlsPacketSeq(broadcast:CBroadcast) : seq<RslPacket>
    requires CBroadcastIsAbstractable(broadcast)
  {
    match broadcast
    case CBroadcast(_,_,_) => BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src),
                                              AbstractifyEndPointsToNodeIdentities(broadcast.dsts),
                                              AbstractifyCMessageToRslMessage(broadcast.msg))
    case CBroadcastNop => []
  }

  datatype OutboundPackets = Broadcast(broadcast:CBroadcast) | OutboundPacket(p:Option<CPacket>) | PacketSequence(s:seq<CPacket>)

  predicate OutboundPacketsValid(c:OutboundPackets)
  {
    && OutboundPacketsIsAbstractable(c)
    && (match c
        case Broadcast(broadcast) => CBroadcastValid(broadcast)
        case OutboundPacket(Some(p)) => CPacketIsValid(p)
        case OutboundPacket(None()) => true
        case PacketSequence(s) => forall i :: 0 <= i < |s| ==> CPacketIsValid(s[i]))
  }

  predicate OutboundPacketsIsAbstractable(out:OutboundPackets)
  {
    match out
    case Broadcast(broadcast) => CBroadcastIsAbstractable(broadcast)
    case OutboundPacket(Some(p)) => CPacketIsAbstractable(p)
    case OutboundPacket(None()) => true
    case PacketSequence(s) => forall i :: 0 <= i < |s| ==> CPacketIsAbstractable(s[i])
  }

  function AbstractifyOutboundCPacketsToSeqOfRslPackets(out:OutboundPackets) : seq<RslPacket>
    requires OutboundPacketsIsAbstractable(out)
  {
    match out
    case Broadcast(broadcast) => AbstractifyCBroadcastToRlsPacketSeq(broadcast)
    case OutboundPacket(Some(p)) => [AbstractifyCPacketToRslPacket(p)]
    case OutboundPacket(None()) => []
    case PacketSequence(s) => AbstractifySeq(s, AbstractifyCPacketToRslPacket)
  }

  predicate OutboundPacketsHasCorrectSrc(out:OutboundPackets, me:EndPoint)
  {
    match out
    case Broadcast(CBroadcast(src, _, _)) => src == me
    case Broadcast(CBroadcastNop()) => true
    case OutboundPacket(p) => p.Some? ==> p.v.src == me
    case PacketSequence(s) => (forall p :: p in s ==> p.src == me)
                                           //    case OutboundPacket(Some(p)) => p.src == me
                                           //    case OutboundPacket(None()) => true
  }
}
