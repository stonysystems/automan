include "AppInterface.i.dfy"
include "../../Protocol/ByzRSL/Executor.i.dfy"
include "../../Protocol/ByzRSL/Message.i.dfy"
include "Broadcast.i.dfy"
include "CStateMachine.i.dfy"
include "../Common/Util.i.dfy"
include "../../Protocol/ByzRSL/StateMachine.i.dfy"
include "../../Common/Collections/Assumes.i.dfy"

module LiveByzRSL__ExecutorModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__CMessage_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__CConfiguration_i
  import opened LiveByzRSL__Environment_i
  import opened LiveByzRSL__Executor_i
  import opened LiveByzRSL__Message_i
  import opened LiveByzRSL__PacketParsing_i
  import opened LiveByzRSL__ConstantsState_i
  import opened LiveByzRSL__StateMachine_i
  import opened LiveByzRSL__Types_i
  import opened Impl__LiveByzRSL__Broadcast_i
  import opened Common__NodeIdentity_i
  import opened Common__UdpClient_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened Concrete_NodeIdentity_i
  import opened Collections__Maps_i
  import opened Logic__Option_i
  import opened Environment_s
  import opened AppStateMachine_i
  import opened Temporal__Temporal_s
  import opened LiveByzRSL__CStateMachine_i
  import opened GenericRefinement_i
  import opened Common_Assume_i

/************************** AutoMan Translation ************************/

	/** 9 + 0 */
	datatype COutstandingOperation = 
	COutstandingOpKnown(
		v: CRequestBatch, 
		bal: CBallot
	)
	 | 
	COutstandingOpUnknown(
		
	)

	/** 0 + 6 */
	predicate COutstandingOperationIsValid(s: COutstandingOperation) 
	{
		match s
		case COutstandingOpKnown(v, bal) => COutstandingOperationIsAbstractable(s) && CRequestBatchIsValid(s.v) && CBallotIsValid(s.bal)
		case COutstandingOpUnknown() => COutstandingOperationIsAbstractable(s)

	}

	/** 0 + 6 */
	predicate COutstandingOperationIsAbstractable(s: COutstandingOperation) 
	{
		match s
		case COutstandingOpKnown(v, bal) => CRequestBatchIsAbstractable(s.v) && CBallotIsAbstractable(s.bal)
		case COutstandingOpUnknown() => true

	}

	/** 0 + 7 */
	function AbstractifyCOutstandingOperationToOutstandingOperation(s: COutstandingOperation) : OutstandingOperation 
		requires COutstandingOperationIsAbstractable(s)
	{
		match s
		case COutstandingOpKnown(v, bal) => OutstandingOpKnown(AbstractifyCRequestBatchToRequestBatch(s.v), AbstractifyCBallotToBallot(s.bal))
		case COutstandingOpUnknown() => OutstandingOpUnknown()

	}

	/** 8 + 0 */
	datatype CExecutor = 
	CExecutor(
		constants: CReplicaConstants, 
		app: CAppState, 
		ops_complete: int, 
		max_bal_reflected: CBallot, 
		next_op_to_execute: COutstandingOperation, 
		ghost reply_cache: CReplyCache
	)

	/** 0 + 13 */
	predicate CExecutorIsValid(s: CExecutor) 
	{
		CExecutorIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CAppStateIsValid(s.app) 
		&& 
		CBallotIsValid(s.max_bal_reflected) 
		&& 
		COutstandingOperationIsValid(s.next_op_to_execute) 
		&& 
		CReplyCacheIsValid(s.reply_cache)
	}

	/** 0 + 12 */
	predicate CExecutorIsAbstractable(s: CExecutor) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CAppStateIsAbstractable(s.app) 
		&& 
		CBallotIsAbstractable(s.max_bal_reflected) 
		&& 
		COutstandingOperationIsAbstractable(s.next_op_to_execute) 
		&& 
		CReplyCacheIsAbstractable(s.reply_cache)
	}

	/** 0 + 5 */
	function AbstractifyCExecutorToLExecutor(s: CExecutor) : LExecutor 
		requires CExecutorIsAbstractable(s)
	{
		LExecutor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCAppStateToAppState(s.app), s.ops_complete, AbstractifyCBallotToBallot(s.max_bal_reflected), AbstractifyCOutstandingOperationToOutstandingOperation(s.next_op_to_execute), AbstractifyCReplyCacheToReplyCache(s.reply_cache))
	}

	/** 15 + 2 */
	function method CExecutorInit(c: CReplicaConstants) : CExecutor 
		requires CReplicaConstantsIsValid(c)
		ensures var s := CExecutorInit(c); CExecutorIsValid(s) && LExecutorInit(AbstractifyCExecutorToLExecutor(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			CAppStateInit(); 		
		var t3 := 
			0; 		
		var t4 := 
			CBallot(0, 0); 		
		var t5 := 
			COutstandingOpUnknown(); 		
		var t6 := 
			map[]; 		
		CExecutor(t1, t2, t3, t4, t5, t6)
	}

	/** 6 + 7 */
	function method CExecutorGetDecision(s: CExecutor, bal: CBallot, opn: COperationNumber, v: CRequestBatch) : CExecutor 
		requires CExecutorIsValid(s)
		requires CBallotIsValid(bal)
		requires COperationNumberIsValid(opn)
		requires CRequestBatchIsValid(v)
		requires opn == s.ops_complete
		requires s.next_op_to_execute.COutstandingOpUnknown?
		ensures var s' := CExecutorGetDecision(s, bal, opn, v); CExecutorIsValid(s') && LExecutorGetDecision(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCBallotToBallot(bal), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCRequestBatchToRequestBatch(v))
	{
		// var t1 := 
			s.(next_op_to_execute := COutstandingOpKnown(v, bal))	
		// t1
	}

	/** 7 + 10 + 3 */
	function method CGetPacketsFromReplies(me: EndPoint, requests: seq<CRequest>, replies: seq<CReply>) : seq<CPacket> //OutboundPackets 
		requires EndPointIsValid(me)
		requires CRequestBatchIsValid(requests) /** Manually Added */
		requires (forall i :: i in requests ==> CRequestIsValid(i))
		requires (forall i :: i in replies ==> i.CReply? && CReplyIsValid(i))/** Manually Modified */
		requires |requests| == |replies|
		ensures (forall p :: p in CGetPacketsFromReplies(me, requests, replies) ==> p.src == me && p.msg.CMessage_Reply? && CPacketIsAbstractable(p))
		ensures 
			var lr := GetPacketsFromReplies(AbstractifyEndPointToNodeIdentity(me), AbstractifySeq(requests, AbstractifyCRequestToRequest), AbstractifySeq(replies, AbstractifyCReplyToReply)); 
			var cr := CGetPacketsFromReplies(me, requests, replies); 
			&& AbstractifySeq(cr, AbstractifyCPacketToRslPacket) == (lr)
	{
		if |requests| == 0 then 
			[] 
		else 
			[CPacket(requests[0].client, me, CMessage_Reply(requests[0].seqno, replies[0].reply))] + CGetPacketsFromReplies(me, requests[1 .. ], replies[1 .. ])
	}

	/** 10 + 10 + 2 */
	function method CClientsInReplies(replies: seq<CReply>) : CReplyCache 
		requires (forall i :: i in replies ==> i.CReply? && CReplyIsValid(i))/** Manually Modified */
		ensures 
			var m := CClientsInReplies(replies); 
			(forall c :: c in m ==> m[c].client == c) 
			&& (forall c :: c in m ==> (exists req_idx :: 0 <= req_idx && req_idx < |replies| && replies[req_idx].client == c && m[c] == replies[req_idx]))
		ensures 
			var lr := LClientsInReplies(AbstractifySeq(replies, AbstractifyCReplyToReply)); 
			var cr := CClientsInReplies(replies); 
			CReplyCacheIsValid(cr) 
			&& (AbstractifyCReplyCacheToReplyCache(cr)) == (lr)
	{
		var r := 
		if |replies| == 0 then 
			map[] 
		else 
			CClientsInReplies(replies[1 .. ])[replies[0].client := replies[0]];
		lemma_ReplyCacheLen(r);/** Manually Added */
		r
	}

	/** 10 + 3 + 2 */
	function method CUpdateNewCache(c: CReplyCache, replies: seq<CReply>) : CReplyCache 
		requires CReplyCacheIsValid(c)
		requires forall i :: 0 <= i < |replies| ==> CReplyIsValid(replies[i])/** Manually Added */
		ensures var c' := CUpdateNewCache(c, replies); CReplyCacheIsValid(c') && UpdateNewCache(AbstractifyCReplyCacheToReplyCache(c), AbstractifyCReplyCacheToReplyCache(c'), AbstractifySeq(replies, AbstractifyCReplyToReply))
	{
		var t1 := 
			var nc := 
				CClientsInReplies(replies); 			
			var t1 := 
				(map client | client in c.Keys + nc.Keys :: if client in c then c[client] else nc[client]); 			
			t1; 		
		lemma_ReplyCacheLen(t1);/** Manually Added */
		t1
	}

	/** 41 + 5 + 1 */
	function method CExecutorExecute(s: CExecutor) : (CExecutor, OutboundPackets) 
		requires CExecutorIsValid(s)
		requires s.next_op_to_execute.COutstandingOpKnown?
		requires CLtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val)
		requires CReplicaConstantsValid(s.constants)
		ensures var (s', non_empty_sequential_sent_packets) := CExecutorExecute(s); CExecutorIsValid(s') && OutboundPacketsIsValid(non_empty_sequential_sent_packets) && LExecutorExecute(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(non_empty_sequential_sent_packets))
	{
		var t1 := 
			var batch := 
				s.next_op_to_execute.v; 			
			var t1 := 
				var temp := 
					CHandleRequestBatch(s.app, batch); 				
				var t1 := 
					var new_state := 
						temp.0[|temp.0| - 1]; 					
					var t1 := 
						var replies := 
							temp.1; 						
						var t1 := 
							var clients := 
								CClientsInReplies(replies); 							
							var t1 := 
								s.constants; 							
							var t2 := 
								new_state; 							
							var t3 := 
								s.ops_complete + 1; 							
							var t4 := 
								if CBalLeq(s.max_bal_reflected, s.next_op_to_execute.bal) then 
									s.next_op_to_execute.bal 
								else 
									s.max_bal_reflected; 							
							var t5 := 
								COutstandingOpUnknown(); 							
							var t6 := 
								CUpdateNewCache(s.reply_cache, replies); 							
							var t7 := 
								PacketSequence(CGetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies)); 							
							(CExecutor(t1, t2, t3, t4, t5, t6), t7); 					
						(t1.0, t1.1); 					
					(t1.1, t1.0); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		lemma_ReplyCacheLen(t1.1.reply_cache);	/** Manually Added */
		(t1.1, t1.0)
	}

	/** 16 + 4 */
	function method CExecutorProcessStartingPhase2(s: CExecutor, inp: CPacket) : (CExecutor, OutboundPackets) 
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_StartingPhase2?
		ensures var (s', broadcast_sent_packets) := CExecutorProcessStartingPhase2(s, inp); CExecutorIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LExecutorProcessStartingPhase2(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := 
			if inp.src in s.constants.all.config.replica_ids && inp.msg.logTruncationPoint_2 > s.ops_complete then 
				var t1 := 
					s; 				
				var t2 := 
					Broadcast(CBroadcastNop);
					// Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_AppStateRequest(inp.msg.bal_2, inp.msg.logTruncationPoint_2))); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					Broadcast(CBroadcastNop); 				
				(t1, t2); 		
		(t1.0, t1.1)
	}

	method CExecutorProcessRequest(s: CExecutor, inp: CPacket, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns (sequential_sent_packets:OutboundPackets)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Request?
		requires inp.src in s.reply_cache
		requires s.reply_cache[inp.src].CReply?
		requires inp.msg.seqno_req <= s.reply_cache[inp.src].seqno
		
		/** Manually Added for I1 */
		requires MutableMap.MapOf(reply_cache_mutable) == s.reply_cache

		ensures OutboundPacketsIsValid(sequential_sent_packets) && LExecutorProcessRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var contains, r := reply_cache_mutable.TryGetValue(inp.src); /** Manually Added for I1 */

		// var t1 := 
			if inp.msg.seqno_req == r.seqno /*&& CReplicaConstantsValid(s.constants)*/ { 
				// var t1 := 
					// var r := 
					// 	s.reply_cache[inp.src]; 					
					sequential_sent_packets := 
						PacketSequence([CPacket(r.client, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_Reply(r.seqno, r.reply))]); 					
					// t1; 				
				// t1 
			} else { 
				sequential_sent_packets := 
					PacketSequence([]); 				
				// t1; 		
			}
		// sequential_sent_packets := t1;
	}

/************************** AutoMan Translation End ************************/


/************************** Manually Optimization for I1 ********************/
	/** 9 */
	method CExecutorExecute_I1(cs:CExecutor, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns(cs':CExecutor, cout:OutboundPackets)
		requires cs.next_op_to_execute.COutstandingOpKnown?
		requires CExecutorIsValid(cs)
		requires MutableMap.MapOf(reply_cache_mutable) == cs.reply_cache
		requires CLtUpperBound(cs.ops_complete, cs.constants.all.params.max_integer_val)
		modifies reply_cache_mutable
		ensures CExecutorIsValid(cs')
		ensures  OutboundPacketsIsValid(cout)
		ensures  OutboundPacketsHasCorrectSrc(cout, cs.constants.all.config.replica_ids[cs.constants.my_index])
		ensures OutboundPacketsIsAbstractable(cout)
		ensures var (cs'_0, cout_0) := CExecutorExecute(cs);
				&& cs' == cs'_0
				&& cout == cout_0
		// ensures LExecutorExecute(AbstractifyCExecutorToLExecutor(cs), 
		//                         AbstractifyCExecutorToLExecutor(cs'), 
		//                         AbstractifyOutboundCPacketsToSeqOfRslPackets(cout))
		// ensures  cs.constants == cs'.constants
		ensures  cs'.reply_cache == MutableMap.MapOf(reply_cache_mutable)
	{
		ghost var cstates:seq<CAppState>, newReplyCache:CReplyCache;
		var new_state:CAppState, replies:seq<CReply>;
		var batch := cs.next_op_to_execute.v;
		cstates, new_state, replies, newReplyCache := CHandleRequestBatch_I1(cs.app, batch, cs.reply_cache, reply_cache_mutable);

		ghost var (states_0, replies_0) := CHandleRequestBatch(cs.app, batch);
		assert states_0 == cstates;
		assert replies_0 == replies;
		assert new_state == cstates[|cstates|-1];
		ghost var clients := CClientsInReplies(replies_0);
		ghost var new_cache := CUpdateNewCache(cs.reply_cache, replies);
		//   ghost var keyset := clients.Keys + cs.reply_cache.Keys;
		//   ghost var new_cache := (map c | c in keyset :: if c in clients then clients[c] else cs.reply_cache[c]);
		// var packets := CGetPacketsFromReplies_I0(cs.constants.all.config.replica_ids[cs.constants.my_index], batch, replies);

		cs' := cs.(
			app := new_state,
			ops_complete := cs.ops_complete + 1,
			max_bal_reflected := (if CBalLeq(cs.max_bal_reflected, cs.next_op_to_execute.bal) then cs.next_op_to_execute.bal else cs.max_bal_reflected),
			next_op_to_execute := COutstandingOpUnknown(),
			reply_cache := newReplyCache
		);

		lemma_ReplyCacheLen(cs'.reply_cache);

		ghost var cs'_0 := cs.(
			app := states_0[|states_0|-1],
			ops_complete := cs.ops_complete + 1,
			max_bal_reflected := (if CBalLeq(cs.max_bal_reflected, cs.next_op_to_execute.bal) then cs.next_op_to_execute.bal else cs.max_bal_reflected),
			next_op_to_execute := COutstandingOpUnknown(),
			reply_cache := new_cache
		);

		assert forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, cs.reply_cache, newReplyCache, batch, replies);
		// assume forall client :: client in new_cache ==> ReplyCacheUpdated(client, cs.reply_cache, new_cache, batch, replies);
		// assume |newReplyCache| == |new_cache|;
		// assume newReplyCache == new_cache;

		lemma_CExecutorExecute_I1(newReplyCache, new_cache);

		assert cs'_0 == cs';

		assert cs'_0 == CExecutorExecute(cs).0;

		// cout := PacketSequence([]);
		var packets := CGetPacketsFromReplies(cs.constants.all.config.replica_ids[cs.constants.my_index], batch, replies);
		cout := PacketSequence(packets);
	}

	/** 29 */
	method {:timeLimitMultiplier 2} CHandleRequestBatch_I1(state:CAppState, batch:CRequestBatch, ghost reply_cache:CReplyCache, reply_cache_mutable:MutableMap<EndPoint, CReply>) 
		returns (ghost states:seq<CAppState>, final_state:CAppState, replies_seq:seq<CReply>, ghost newReplyCache:CReplyCache)
		requires CRequestBatchIsValid(batch)
		requires CReplyCacheIsValid(reply_cache)
		requires MutableMap.MapOf(reply_cache_mutable) == reply_cache
		modifies reply_cache_mutable
		ensures |states| == |batch|+1 
		ensures |replies_seq| == |batch|
		ensures states[0] == state
		ensures states[|states|-1]==final_state
		ensures CReplyCacheIsAbstractable(newReplyCache)
		ensures (forall i :: 0 <= i < |batch| ==>
						&& replies_seq[i].CReply?
						&& ((states[i+1], replies_seq[i].reply) == HandleAppRequest(states[i], batch[i].request))
						&& replies_seq[i].client == batch[i].client
						&& replies_seq[i].seqno == batch[i].seqno)
				&& (forall i :: 0 <= i < |replies_seq| ==> CReplyIsValid(replies_seq[i]))
		ensures forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch, replies_seq)
		ensures newReplyCache == MutableMap.MapOf(reply_cache_mutable);
		ensures var (states_0, replies_0) := CHandleRequestBatch(state,batch); /** Refines I0 */
				states == states_0 
				&& replies_0 == replies_seq
	{
		ghost var (states_0, replies_0) := CHandleRequestBatch(state,batch);
		var i:uint64 := 0;
		states := [state];
		final_state := state;
		ghost var replies:seq<CReply> := [];
		var repliesArr := new CReply[|batch| as uint64];
		newReplyCache := reply_cache;
		while i < |batch| as uint64
			invariant 0 <= i as int <= |batch|
			invariant |replies| == i as int
			invariant |states| == (i as int) + 1
			invariant states[0] == state
			invariant final_state == states[i]
			invariant (forall j :: 0 <= j < |replies| ==> 
						&& replies[j].CReply?
						&& ((states[j+1], replies[j].reply) == HandleAppRequest(states[j], batch[j].request))
						&& replies[j].client == batch[j].client
						&& replies[j].seqno == batch[j].seqno
						&& replies[j] == repliesArr[j])
			invariant (forall j :: 0 <= j < i as int ==> States_Equal(j, batch, states, replies, states_0))
			invariant (forall j :: 0 <= j < i as int ==> states[j+1] == states_0[j+1])
			invariant replies == replies_0[..i]
			invariant CReplyCacheIsValid(newReplyCache)
			invariant forall client {:trigger ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)} :: 
							client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)
			invariant MutableMap.MapOf(reply_cache_mutable) == newReplyCache
		{
		ghost var old_replies := replies;
		ghost var old_states := states;
		ghost var old_newReplyCache := newReplyCache;

		// assert forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);

		var (new_state, reply) := HandleAppRequest(final_state, batch[i].request);
		var newReply := CReply(batch[i].client, batch[i].seqno, reply);

		assert (forall j :: 0 <= j < |replies| ==> replies[j] == repliesArr[j]);
		ghost var k := |replies|;
		replies := replies + [newReply];
		repliesArr[i] := newReply;
		assert replies[|replies| - 1] == repliesArr[|replies| - 1];
		// assert |replies| == i as int;
		assert replies[i] == newReply;
		assert repliesArr[i] == newReply;
		assert replies[k] == repliesArr[k];
		assert |replies| == k + 1;
		assert (forall j :: 0 <= j < |replies| ==> replies[j] == repliesArr[j]);
		states := states + [new_state];
		final_state := new_state;

		ghost var slimReplyCache:CReplyCache;
		var staleEntry;
		var cache_size := reply_cache_mutable.SizeModest();
		if cache_size == 255 as uint64 {    // max_reply_cache_size()
			staleEntry :| staleEntry in MutableMap.MapOf(reply_cache_mutable);      // TODO: Choose based on age // TODO: This is very inefficient.  Optimize value selection.
			slimReplyCache := RemoveElt(newReplyCache, staleEntry);
			reply_cache_mutable.Remove(staleEntry);
		} else {
			slimReplyCache := newReplyCache;
		}
		assert CReplyCacheIsValid(slimReplyCache);
		newReplyCache := slimReplyCache[batch[i].client := newReply];
		reply_cache_mutable.Set(batch[i].client, newReply);
		// lemma_CHandleRequestBatch_I1_loop(batch, replies, i as int, states, state, final_state, repliesArr,
		// 											states_0, replies_0, newReplyCache, reply_cache, reply_cache_mutable);
		  assert MutableMap.MapOf(reply_cache_mutable) == newReplyCache;
		  forall e {:trigger EndPointIsValidIPV4(e)} | e in newReplyCache 
		    ensures EndPointIsValidIPV4(e) && CReplyIsAbstractable(newReplyCache[e])
		  {
		    if (e == batch[i].client) {
		    }
		  }

		  assert CReplyCacheIsValid(newReplyCache);
		  ghost var r_newReplyCache := newReplyCache;
		  ghost var r_replyCache := old_newReplyCache;
		  forall client | client in r_newReplyCache
		    // ensures || (client in r_replyCache && r_newReplyCache[client] == r_replyCache[client])
		    //         // || ExistsReqIdx((i as int)+1, replies, old_newReplyCache, newReplyCache, client)
		    //         || (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch, replies))
		    ensures ReplyCacheUpdated(client, old_newReplyCache, newReplyCache, batch[..(i as int)+1], replies)
		  {
		    var e := client;
		    if e == batch[i].client {
		      assert replies[i].client == replies[i].client;
		      assert replies[i].client == client && r_newReplyCache[client] == replies[i];
		      // assert ExistsReqIdx((i as int)+1, replies, old_newReplyCache, newReplyCache, client);
		      assert ClientIndexMatches(i as int, e, newReplyCache, batch[..(i as int)+1], replies);
		      assert ReplyCacheUpdated(client, old_newReplyCache, newReplyCache, batch[..(i as int)+1], replies);
		    } 
		    else {
		      assert e in old_newReplyCache;
		      if |old_newReplyCache| == 0x1_0000_0000 - 1 {
		        assert e !in slimReplyCache;
						
		        assert e !in newReplyCache;
		        assert e !in r_newReplyCache;
		        assert false;
		      } else {
		        assert e in slimReplyCache;
		      }
		      assert e in slimReplyCache;
			
		      assert newReplyCache[e] == old_newReplyCache[e];
		      assert newReplyCache[e] == newReplyCache[e];
		      assert old_newReplyCache[e] == old_newReplyCache[e];
		      assert ReplyCacheUpdated(client, old_newReplyCache, newReplyCache, batch[..(i as int)+1], replies);
		    }
		  }
		
		i := i + 1;

	      if i > 1 {
	        calc {
	          states[i-1];
	            { assert States_Equal((i as int)-2, batch, old_states, old_replies, states_0); }
	          states_0[i-1];
	        }
	      } else {
	        calc {
	          states[i-1];
	          states[0];
	          states_0[0];
	          states_0[i-1];
	        }
	      }

	      forall j | 0 <= j < i as int 
	        ensures States_Equal(j, batch, states, replies, states_0)
	        ensures states[j+1] == states_0[j+1]
	      {
	        if j < (i as int) - 1 {
	          assert States_Equal(j, batch, old_states, old_replies, states_0);    // From the loop invariant
	          assert States_Equal(j, batch, states, replies, states_0);
	        } else {

	          calc {
	            states[j+1];
	            states[i];
	            new_state;
	            HandleAppRequest(states[i-1], batch[i-1].request).0;
	            calc {
	              batch[i-1].request;
	              batch[i-1].request;
	            }
	            HandleAppRequest(states_0[i-1], batch[i-1].request).0;
	            states_0[i];
	            states_0[j+1];
	          }
	        }
	      }

	    //   ghost var g_replies_prefix := replies_0[..i];
	    //   forall k | 0 <= k < |replies|
	    //     ensures replies[k] == g_replies_prefix[k]
	    //   {
	    //     if k < |replies| - 1 {
	    //       assert old_replies == replies_0[..i-1];
	    //     } else {
	    //       assert k == (i as int) - 1;
	    //       ghost var reply' := HandleAppRequest(states[i-1], batch[i-1].request).1;
	    //       calc {
	    //         replies[k];
	    //         replies[k];
	    //         CReply(batch[i-1].client, batch[i-1].seqno, reply');
	    //         CReply(batch[i-1].client, batch[i-1].seqno, 
	    //               HandleAppRequest(states_0[i-1], batch[i-1].request).1);
	    //           { lemma_HandleBatchProperties(state,
	    //                                               batch, 
	    //                                               states_0, replies_0, (i as int)-1); } 
	    //         g_replies_prefix[k];
	    //       }
	    //     }
	    //   }
	    //   assert replies == g_replies_prefix;

	      assert forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, old_newReplyCache, newReplyCache, batch[..i], replies);
	      forall client | client in newReplyCache
	        ensures ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)
	      {
	        assert ReplyCacheUpdated(client, old_newReplyCache, newReplyCache, batch[..i], replies);
	        assert || (client in old_newReplyCache && newReplyCache[client] == old_newReplyCache[client])
	              || (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies));

	        if client in old_newReplyCache {
	          assert ReplyCacheUpdated(client, reply_cache, old_newReplyCache, batch[..i-1], old_replies);
	  //        assert || (client in reply_cache && old_newReplyCache[client] == reply_cache[client])
	  //               || (exists req_idx :: ClientIndexMatches(req_idx, client, old_newReplyCache, batch[..i-1], old_replies));
	          if client in reply_cache && old_newReplyCache[client] == reply_cache[client] {
	            if client in old_newReplyCache && newReplyCache[client] == old_newReplyCache[client] {
	              assert client in reply_cache && newReplyCache[client] == reply_cache[client];
	              assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
	            } else {
	              ghost var req_idx :| ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies);
	              assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
	            }
	          } else {
	            ghost var req_idx :| ClientIndexMatches(req_idx, client, old_newReplyCache, batch[..i-1], old_replies);
	            assert && 0 <= req_idx < |batch[..i-1]| 
	                  && replies[req_idx].client == client 
	                  && old_newReplyCache[client] == replies[req_idx];
	            if client in old_newReplyCache && newReplyCache[client] == old_newReplyCache[client] {
	              assert ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies);
	            } else {
	              ghost var req_idx' :| ClientIndexMatches(req_idx', client, newReplyCache, batch[..i], replies);
	            }
	            assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
	          }
	        }

	        assert || (client in reply_cache && newReplyCache[client] == reply_cache[client])
	              || (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies));
	      }
		//   assert MutableMap.MapOf(reply_cache_mutable) == newReplyCache;
		//   assert forall client  :: 
        //             client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
		//   assert replies == replies_0[..i];
      	//   assert CReplyCacheIsValid(newReplyCache);
		//   assert (forall j :: 0 <= j < i as int ==> states[j+1] == states_0[j+1]);
		//   assert (forall j :: 0 <= j < i as int ==> States_Equal(j, batch, states, replies, states_0));
		//   assert 0 <= i as int <= |batch|;
		//   assert |replies| == i as int;
		//   assert |states| == (i as int) + 1;
		//   assert states[0] == state;
		//   assert final_state == states[i];
		//   assert (forall j :: 0 <= j < |replies| ==> 
        //           && replies[j].CReply?
		// 		&& ((states[j+1], replies[j].reply) == HandleAppRequest(states[j], batch[j].request))
		// 		&& replies[j].client == batch[j].client
		// 		&& replies[j].seqno == batch[j].seqno
		// 		&& replies[j] == repliesArr[j]
		// 		);
		  lemma_CHandleRequestBatch_I1_loop(batch, replies, i as int, states, state, final_state, repliesArr,
													states_0, replies_0, newReplyCache, reply_cache, reply_cache_mutable);
		}
		replies_seq := repliesArr[..];
		forall client | client in newReplyCache
		  ensures replies_seq == replies
		  ensures ReplyCacheUpdated(client, reply_cache, newReplyCache, batch, replies)
		{
		  assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
		  assert i as int == |batch|;
		  assert batch[..i] == batch;
		}
		// lemma_CHandleRequestBatch_I1(state, batch, reply_cache, reply_cache_mutable, states, final_state, replies_seq, newReplyCache);
		lemma_StatesEqual(states, states_0);
	}

	lemma lemma_HandleBatchProperties(state:AppState, batch:CRequestBatch, states:seq<CAppState>, replies:seq<CReply>, i:int)
		requires CRequestBatchIsValid(batch)
		requires (states, replies) == CHandleRequestBatch(state, batch)
		requires 0 <= i < |batch|
		ensures  states[0] == state
		ensures  |states| == |batch| + 1
		ensures  |replies| == |batch|
		ensures  replies[i].CReply?
		ensures  var (s, r) := HandleAppRequest(states[i], batch[i].request);
				s == states[i+1] && r == replies[i].reply
		ensures  replies[i].client == batch[i].client
		ensures  replies[i].seqno == batch[i].seqno
	{
		assert states == CHandleRequestBatchHidden(state, batch).0;         // OBSERVE
		assert replies == CHandleRequestBatchHidden(state, batch).1;        // OBSERVE
		assert (states, replies) == CHandleRequestBatchHidden(state, batch);
		lemma_CHandleRequestBatchHidden(state, batch, states,replies);
	}

	predicate ReplyCacheUpdated(client:EndPoint, oldReplyCache:CReplyCache, newReplyCache:CReplyCache, batch:CRequestBatch, replies:seq<CReply>) 
		requires client in newReplyCache
		requires |batch| == |replies|
	{
		|| (client in oldReplyCache && newReplyCache[client] == oldReplyCache[client])
		|| (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch, replies))
	}

	predicate ClientIndexMatches(req_idx:int, client:EndPoint, newReplyCache:CReplyCache, batch:CRequestBatch, replies:seq<CReply>) 
		requires |batch| == |replies|
		requires client in newReplyCache
	{
		0 <= req_idx < |batch| && replies[req_idx].client == client && newReplyCache[client] == replies[req_idx] 
	}

	predicate States_Equal(j:int, batch:CRequestBatch, states:seq<CAppState>, replies:seq<CReply>, g_states:seq<CAppState>)
		requires 0 <= j < |batch|
		requires 0 <= j < |states|-1
		requires 0 <= j < |g_states|-1
		requires 0 <= j < |replies|
	{
		&& states[j+1] == g_states[j+1]
		&& replies[j].CReply?
		&& ((states[j+1], replies[j].reply) == HandleAppRequest(states[j], batch[j].request))
		&& replies[j].client == batch[j].client
		&& replies[j].seqno == batch[j].seqno
	}

	lemma lemma_StatesEqual(states:seq<CAppState>, states_0:seq<CAppState>)
		requires |states| == |states_0|
		requires |states| > 0
		requires states[0] == states_0[0]
		requires forall j :: 0 <= j < |states| - 1 ==> states[j+1] == states_0[j+1]
		ensures forall j :: 1 <= j < |states| ==> states[j] == states_0[j]
		ensures forall j :: 0 <= j < |states| ==> states[j] == states_0[j]
	{
		forall j | 1 <= j < |states|
			ensures states[j] == states_0[j]
		{
			var k := j - 1;
			assert 0 <= k < |states| - 1;
			assert states[k+1] == states_0[k+1];
			assert states[j] == states_0[j];
		}
		assert forall j :: 1 <= j < |states| ==> states[j] == states_0[j];
	}

	// lemma {:axiom} lemma_CHandleRequestBatch_I1(state:CAppState, batch:CRequestBatch, reply_cache:CReplyCache, reply_cache_mutable:MutableMap<EndPoint, CReply>,
	// 		states:seq<CAppState>, final_state:CAppState, replies_seq:seq<CReply>, newReplyCache:CReplyCache)
	// 		requires CRequestBatchIsValid(batch)
	// 	requires CReplyCacheIsValid(reply_cache)
	// 	//   requires MutableMap.MapOf(reply_cache_mutable) == reply_cache
	// 	//   modifies reply_cache_mutable
	// 	ensures |states| == |batch|+1 
	// 	ensures |replies_seq| == |batch|
	// 	ensures states[0] == state
	// 	ensures states[|states|-1]==final_state
	// 	ensures CReplyCacheIsAbstractable(newReplyCache)
	// 	ensures (forall i :: 0 <= i < |batch| ==>
	// 					&& replies_seq[i].CReply?
	// 					&& ((states[i+1], replies_seq[i].reply) == HandleAppRequest(states[i], batch[i].request))
	// 					&& replies_seq[i].client == batch[i].client
	// 					&& replies_seq[i].seqno == batch[i].seqno)
	// 			&& (forall i :: 0 <= i < |replies_seq| ==> CReplyIsValid(replies_seq[i]))
	// 	ensures forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch, replies_seq)
	// 	ensures newReplyCache == MutableMap.MapOf(reply_cache_mutable);
	// 	ensures var (states_0, replies_0) := CHandleRequestBatch(state,batch);
	// 			states == states_0 
	// 			&& replies_0 == replies_seq

	// lemma {:axiom} lemma_CHandleRequestBatch_I1_loop(batch:CRequestBatch, replies:seq<CReply>, i:int, states:seq<CAppState>, state:CAppState, final_state:CAppState, repliesArr:array<CReply>,
	// 											states_0:seq<CAppState>, replies_0:seq<CReply>, newReplyCache:CReplyCache, reply_cache:CReplyCache, reply_cache_mutable:MutableMap<EndPoint, CReply>)
	// 	requires |states_0| == |batch| + 1
	// 	requires |replies_0| == |batch|
	// 	ensures 0 <= i as int <= |batch|
	// 	ensures |replies| == i as int
	// 	ensures |states| == (i as int) + 1
	// 	ensures states[0] == state
	// 	ensures final_state == states[i]
	// 	ensures repliesArr.Length == |batch|
	// 	ensures (forall j :: 0 <= j < |replies| ==> 
	// 				&& replies[j].CReply?
	// 					&& ((states[j+1], replies[j].reply) == HandleAppRequest(states[j], batch[j].request))
	// 					&& replies[j].client == batch[j].client
	// 					&& replies[j].seqno == batch[j].seqno
	// 					&& replies[j] == repliesArr[j])
	// 	ensures (forall j :: 0 <= j < i as int ==> States_Equal(j, batch, states, replies, states_0))
	// 	ensures (forall j :: 0 <= j < i as int ==> states[j+1] == states_0[j+1])
	// 	ensures replies == replies_0[..i]
	// 	ensures CReplyCacheIsValid(newReplyCache)
	// 	ensures forall client {:trigger ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)} :: 
	// 					client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)
	// 	ensures MutableMap.MapOf(reply_cache_mutable) == newReplyCache

	// lemma {:axiom} lemma_CExecutorExecute_I1(newReplyCache:CReplyCache, new_cache:CReplyCache)
  	// 	ensures newReplyCache == new_cache
/************************** Manually Optimization for I1 End ********************/

  lemma {:axiom} lemma_ReplyCacheLen(cache:CReplyCache)
    ensures |cache| < max_reply_cache_size()

}