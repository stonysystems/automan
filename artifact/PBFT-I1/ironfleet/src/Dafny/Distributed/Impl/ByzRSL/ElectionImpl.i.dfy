include "../../Protocol/ByzRSL/Election.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "CConfiguration.i.dfy"
include "CConstants.i.dfy"
include "../Common/Util.i.dfy"
include "../Common/UpperBound.i.dfy"

module LiveByzRSL__ElectionModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__CMessage_i
  // import opened LiveByzRSL__CMessageRefinements_i
  import opened LiveByzRSL__Configuration_i
  import opened LiveByzRSL__ConstantsState_i
  import opened LiveByzRSL__CConfiguration_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__Election_i
  import opened LiveByzRSL__Types_i
  import opened Common__NodeIdentity_i
  import opened Common__SeqIsUnique_i
  import opened Common__SeqIsUniqueDef_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened Collections__Seqs_s
  import opened Collections__Sets_i
  import opened Collections__Maps_i
  import opened GenericRefinement_i
  import opened LiveByzRSL__AppInterface_i

  /************************** AutoMan Translation ************************/
  
  /** 10 + 0 */
  datatype CElectionState = 
	CElectionState(
		constants: CReplicaConstants, 
		current_view: CBallot, 
		current_view_suspectors: set<int>, 
		epoch_end_time: int, 
		epoch_length: int, 
		requests_received_this_epoch: seq<CRequest>, 
		requests_received_prev_epochs: seq<CRequest>,

		/** I1 */
		ghost cur_req_set:set<CRequestHeader>,
		ghost prev_req_set:set<CRequestHeader>,
    cur_req_map:map<CRequestHeader, CAppMessage>,
    prev_req_map:map<CRequestHeader, CAppMessage>
	)

  /** 0 + 12 */
	predicate CElectionStateIsValid(s: CElectionState) 
	{
		CElectionStateIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CBallotIsValid(s.current_view) 
		&& 
		(forall i :: i in s.requests_received_this_epoch ==> CRequestIsValid(i)) 
		&& 
		(forall i :: i in s.requests_received_prev_epochs ==> CRequestIsValid(i))
	}

  /** 0 + 10 */
	predicate CElectionStateIsAbstractable(s: CElectionState) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CBallotIsAbstractable(s.current_view) 
		&& 
		(forall i :: i in s.requests_received_this_epoch ==> CRequestIsAbstractable(i)) 
		&& 
		(forall i :: i in s.requests_received_prev_epochs ==> CRequestIsAbstractable(i))

		/** I1 */
		&& HeadersMatch(s.requests_received_this_epoch, s.cur_req_set)
		&& HeadersMatch(s.requests_received_prev_epochs, s.prev_req_set)
		&& HeadersMatch(s.requests_received_prev_epochs + s.requests_received_this_epoch, s.prev_req_set + s.cur_req_set)
    && ReqMapMatch(s.requests_received_this_epoch, s.cur_req_map)
    && ReqMapMatch(s.requests_received_prev_epochs, s.prev_req_map)
    && ReqMapMatch(s.requests_received_prev_epochs + s.requests_received_this_epoch, s.prev_req_map + s.cur_req_map)
	}

  /** 0 + 5 */
	function AbstractifyCElectionStateToElectionState(s: CElectionState) : ElectionState 
		requires CElectionStateIsAbstractable(s)
	{
		ElectionState(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.current_view), s.current_view_suspectors, s.epoch_end_time, s.epoch_length, AbstractifySeq(s.requests_received_this_epoch, AbstractifyCRequestToRequest), AbstractifySeq(s.requests_received_prev_epochs, AbstractifyCRequestToRequest))
	}

  /** 6 + 7 */
  function method CComputeSuccessorView(b: CBallot, c: CConstants) : CBallot 
		requires CBallotIsValid(b)
		requires CConstantsIsValid(c)
		ensures 
      var lr := ComputeSuccessorView(AbstractifyCBallotToBallot(b), AbstractifyCConstantsToLConstants(c)); 
      var cr := CComputeSuccessorView(b, c); 
      CBallotIsValid(cr) 
      && (AbstractifyCBallotToBallot(cr)) == (lr)
	{
		if b.proposer_id + 1 < |c.config.replica_ids| then 
			CBallot(b.seqno, b.proposer_id + 1) 
		else 
			CBallot(b.seqno + 1, 0)
	}

  /** 6 + 7 */
  function method CBoundRequestSequence(s: seq<CRequest>, lengthBound: CUpperBound) : seq<CRequest> 
		requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CUpperBoundIsValid(lengthBound)
		ensures 
      var lr := BoundRequestSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCUpperBoundToUpperBound(lengthBound)); 
      var cr := CBoundRequestSequence(s, lengthBound); 
      (forall i :: i in cr ==> CRequestIsValid(i)) 
      && (AbstractifySeq(cr, AbstractifyCRequestToRequest)) == (lr)
	{
		if lengthBound.CUpperBoundFinite? && 0 <= lengthBound.n && lengthBound.n < |s| then 
			s[ .. lengthBound.n] 
		else 
			s
	}

  /** 9 + 3 */
  function method CRequestsMatch(r1: CRequest, r2: CRequest) : bool 
		requires CRequestIsValid(r1)
		requires CRequestIsValid(r2)
		ensures CRequestsMatch(r1, r2) == RequestsMatch(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2))
	{
		r1.CRequest? 
		&& 
		r2.CRequest? 
		&& 
		r1.client == r2.client 
		&& 
		r1.seqno == r2.seqno
	}

  /** 9 + 3 */
	function method CRequestSatisfiedBy(r1: CRequest, r2: CRequest) : bool 
		requires CRequestIsValid(r1)
		requires CRequestIsValid(r2)
		ensures CRequestSatisfiedBy(r1, r2) == RequestSatisfiedBy(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2))
	{
		r1.CRequest? 
		&& 
		r2.CRequest? 
		&& 
		r1.client == r2.client 
		&& 
		r1.seqno <= r2.seqno
	}

  /** 9 + 4 */
  function method CRemoveAllSatisfiedRequestsInSequence(s: seq<CRequest>, r: CRequest) : seq<CRequest> 
		requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CRequestIsValid(r)
    ensures (forall i :: i in CRemoveAllSatisfiedRequestsInSequence(s, r) ==> i.CRequest? && CRequestIsValid(i))
    ensures AbstractifySeq(CRemoveAllSatisfiedRequestsInSequence(s, r), AbstractifyCRequestToRequest) == RemoveAllSatisfiedRequestsInSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCRequestToRequest(r))
	{
		if |s| == 0 then 
			[] 
		else 
			if CRequestSatisfiedBy(s[0], r) then 
        CRemoveAllSatisfiedRequestsInSequence(s[1..], r)
			else 
        [s[0]] + CRemoveAllSatisfiedRequestsInSequence(s[1..], r)
	}

	function method CCheckRequestValidInReqSeq(s: seq<CRequest>, r: CRequest) : bool 
		requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CRequestIsValid(r)
		ensures var lr := CheckRequestValidInReqSeq(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCRequestToRequest(r)); var cr := CCheckRequestValidInReqSeq(s, r); (cr) == (lr)
	{
    exists i :: i in s && CRequestsMatch(i, r) && i.request == r.request
	}

	function method CCheckRequestValid(s: CElectionState, r: CRequest) : bool 
		requires CElectionStateIsValid(s)
		requires CRequestIsValid(r)
		ensures var lr := CheckRequestValid(AbstractifyCElectionStateToElectionState(s), AbstractifyCRequestToRequest(r)); var cr := CCheckRequestValid(s, r); (cr) == (lr)
	{
		CCheckRequestValidInReqSeq(s.requests_received_this_epoch, r) 
		||
		CCheckRequestValidInReqSeq(s.requests_received_prev_epochs, r)
	}

  /** 10 + 3 */
	function method CElectionStateInit(c: CReplicaConstants) : CElectionState 
		requires CReplicaConstantsIsValid(c)
		requires |c.all.config.replica_ids| > 0
		ensures var es := CElectionStateInit(c); CElectionStateIsValid(es) && ElectionStateInit(AbstractifyCElectionStateToElectionState(es), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := c; 		
		var t2 := CBallot(1, 0); 		
		var t3 := {}; 		
		var t4 := 0; 		
		var t5 := c.all.params.baseline_view_timeout_period; 		
		var t6 := []; 		
		var t7 := []; 		

		/** I1 */
		var t8 := {};
    var t9 := {};
    var t10 := map[];
    var t11 := map[];
    var s :=
		CElectionState(t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11);
    assert t6 + t7 == [];
    assert t10 + t11 == map[];
    ghost var ls := AbstractifyCElectionStateToElectionState(s);
    assert ls.constants == AbstractifyCReplicaConstantsToLReplicaConstants(c);
    s
	}

  /** 13 + 6 */
  /** Modified 19 lines for I1 */
  method {:opaque} CElectionStateProcessHeartbeat(es: CElectionState, p: CPacket, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (es':CElectionState) 
		requires CElectionStateIsValid(es)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_Heartbeat?
		// ensures var es' := CElectionStateProcessHeartbeat(es, p, clock);
    /** Manually Added for I1 */
    requires MutableSet.SetOf(cur_req_set) == es.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == es.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures MutableSet.SetOf(cur_req_set) == es'.cur_req_set
    ensures MutableSet.SetOf(prev_req_set) == es'.prev_req_set /** End */

    ensures CElectionStateIsValid(es') 
      && ElectionStateProcessHeartbeat(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCPacketToRslPacket(p), clock)
	{
		// var t1 := 
      if p.src !in es.constants.all.config.replica_ids {
        es' := es; 
        // t1 
      } else {
        // var t1 := 
        var sender_index := CGetReplicaIndex(p.src, es.constants.all.config); 
        // var t1 := 
        if p.msg.bal_heartbeat == es.current_view && p.msg.suspicious { 
          es' := es.(current_view_suspectors := es.current_view_suspectors + {sender_index}); 
          // t1 
        } else { 
          // var t1 := 
          if CBalLt(es.current_view, p.msg.bal_heartbeat) { 
            /** Manually Added for I1 */
            var new_seq := es.requests_received_prev_epochs + es.requests_received_this_epoch;
            ghost var new_set := es.prev_req_set + es.cur_req_set;
            var new_map := es.prev_req_map + es.cur_req_map;
            prev_req_set.AddSet(cur_req_set);
            cur_req_set.RemoveAll();
            new_set := BoundCRequestHeaders(new_seq, new_set, es.constants.all.params.max_integer_val, prev_req_set); /** End */
            new_map := BoundCRequestMap(new_seq, new_map, es.constants.all.params.max_integer_val);
            // assert ReqMapMatch(new_seq, new_map);
            
            // var t1 := 
            var new_epoch_length := UpperBoundedAdditionImpl(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); 
            es' := es.(current_view := p.msg.bal_heartbeat, 
                       current_view_suspectors := if p.msg.suspicious then {sender_index} else {}, 
                       epoch_length := new_epoch_length, 
                       epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), 
                       requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), 
                       requests_received_this_epoch := [],
                      /** Manually Added for I1 */
                      cur_req_set := {},
                      prev_req_set := new_set,
                      cur_req_map := map[],
                      prev_req_map := new_map); /** End */
            assert es'.requests_received_prev_epochs + es'.requests_received_this_epoch == es'.requests_received_prev_epochs;
            assert es'.prev_req_map + es'.cur_req_map == es'.prev_req_map;
            assert ReqMapMatch(CBoundRequestSequence(new_seq, es.constants.all.params.max_integer_val), new_map);
            assert es'.requests_received_prev_epochs == CBoundRequestSequence(new_seq, es.constants.all.params.max_integer_val);
            assert es'.prev_req_map == new_map;
            assert ReqMapMatch(es'.requests_received_prev_epochs, es'.prev_req_map);
            assert ReqMapMatch(es'.requests_received_prev_epochs + es'.requests_received_this_epoch, es'.prev_req_map + es'.cur_req_map);
            assert CElectionStateIsAbstractable(es');

            // lemma_ElectionStateProcessHeartbeat(es, es', p, clock);
            assert ElectionStateProcessHeartbeat(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCPacketToRslPacket(p), clock);
          } else { 
            es' := es; 
            assert CElectionStateIsAbstractable(es);
            assert ReqMapMatch(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.prev_req_map + es.cur_req_map);
            assert ReqMapMatch(es'.requests_received_prev_epochs + es'.requests_received_this_epoch, es'.prev_req_map + es'.cur_req_map);
            assert CElectionStateIsAbstractable(es');
            assert ElectionStateProcessHeartbeat(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCPacketToRslPacket(p), clock);
          }
        }
    }
	}

  	/** 21 + 2 */
	/** 21 lines for I1 */
	method {:opaque} CElectionStateCheckForViewTimeout(es: CElectionState, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (es':CElectionState) 
		requires CElectionStateIsValid(es)
		// ensures var es' := CElectionStateCheckForViewTimeout(es, clock); 
    /** Manually Added for I1 */
		requires MutableSet.SetOf(cur_req_set) == es.cur_req_set
		requires MutableSet.SetOf(prev_req_set) == es.prev_req_set
		modifies cur_req_set, prev_req_set
		ensures MutableSet.SetOf(cur_req_set) == es'.cur_req_set
		ensures MutableSet.SetOf(prev_req_set) == es'.prev_req_set /** End */

    ensures CElectionStateIsValid(es') 
            && ElectionStateCheckForViewTimeout(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), clock)
	{
		// var t1 := 
		if clock < es.epoch_end_time { 
      es' := es; 
      // t1 
		} else {
      // var t1 := 
      if |es.requests_received_prev_epochs| == 0 { 
        // var t1 := 
        var new_epoch_length := es.constants.all.params.baseline_view_timeout_period; 
        prev_req_set.TransferSet(cur_req_set); /** Manually Added for I1 */
        // var t1 := 
        es' := es.(epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := es.requests_received_this_epoch, requests_received_this_epoch := [],
            cur_req_set := {}, /** Manually Added for I1 */
            prev_req_set := es.cur_req_set,
            cur_req_map := map[],
            prev_req_map := es.cur_req_map);  /** Manually Added for I1 */

        assert ReqMapMatch(es.requests_received_this_epoch, es.cur_req_map);
        assert ReqMapMatch(es'.requests_received_this_epoch, es'.cur_req_map);
        assert ReqMapMatch(es'.requests_received_prev_epochs, es'.prev_req_map);
        assert es'.requests_received_prev_epochs + es'.requests_received_this_epoch == es'.requests_received_prev_epochs;
        assert es'.prev_req_map + es'.cur_req_map == es'.prev_req_map;
        assert ReqMapMatch(es'.requests_received_prev_epochs + es'.requests_received_this_epoch, es'.prev_req_map + es'.cur_req_map);
        assert CElectionStateIsAbstractable(es');
        // lemma_ElectionStateCheckForViewTimeout(es, es', clock);
        // t1; 
        // t1 
      } else {
        // var t1 := 
        /** Manually Added for I1 */
        ghost var new_set := es.prev_req_set + es.cur_req_set;
        var new_map := es.prev_req_map + es.cur_req_map;
        prev_req_set.AddSet(cur_req_set);
        cur_req_set.RemoveAll();
        var new_seq := es.requests_received_prev_epochs + es.requests_received_this_epoch;
        new_set := BoundCRequestHeaders(new_seq, new_set, es.constants.all.params.max_integer_val, prev_req_set); /** End */
        new_map := BoundCRequestMap(new_seq, new_map, es.constants.all.params.max_integer_val);

        es' := es.(current_view_suspectors := es.current_view_suspectors + {es.constants.my_index}, epoch_end_time := UpperBoundedAdditionImpl(clock, es.epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := [],
            cur_req_set := {}, /** Manually Added for I1 */
            prev_req_set := new_set,
            cur_req_map := map[],
            prev_req_map := new_map);  /** Manually Added for I1 */
        assert es'.requests_received_prev_epochs + es'.requests_received_this_epoch == es'.requests_received_prev_epochs;
        assert es'.prev_req_map + es'.cur_req_map == es'.prev_req_map;
        assert ReqMapMatch(CBoundRequestSequence(new_seq, es.constants.all.params.max_integer_val), new_map);
        assert es'.requests_received_prev_epochs == CBoundRequestSequence(new_seq, es.constants.all.params.max_integer_val);
        assert es'.prev_req_map == new_map;
        assert ReqMapMatch(es'.requests_received_prev_epochs, es'.prev_req_map);
        assert ReqMapMatch(es'.requests_received_prev_epochs + es'.requests_received_this_epoch, es'.prev_req_map + es'.cur_req_map);
        assert CElectionStateIsAbstractable(es');
        // lemma_ElectionStateCheckForViewTimeout(es, es', clock);
        // t1; 
        // t1; 		
        // t1
			}
    }
	}

	
	/** 10 + 6 */
	/** 16 lines for I1 */
	method {:opaque} CElectionStateCheckForQuorumOfViewSuspicions(es: CElectionState, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (es':CElectionState) 
		requires CElectionStateIsValid(es)
		// ensures var es' := CElectionStateCheckForQuorumOfViewSuspicions(es, clock); 
		requires MutableSet.SetOf(cur_req_set) == es.cur_req_set
		requires MutableSet.SetOf(prev_req_set) == es.prev_req_set
		modifies cur_req_set, prev_req_set 
		ensures MutableSet.SetOf(cur_req_set) == es'.cur_req_set
		ensures MutableSet.SetOf(prev_req_set) == es'.prev_req_set

		ensures CElectionStateIsValid(es') && ElectionStateCheckForQuorumOfViewSuspicions(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), clock)
	{
		// var t1 := 
		if |es.current_view_suspectors| < CMinQuorumSize(es.constants.all.config) || !CLtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val) { 
      es' := es; 
      // t1 
		} else { 
      // var t1 := 
      var new_epoch_length := UpperBoundedAdditionImpl(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); 

      var new_seq := es.requests_received_prev_epochs + es.requests_received_this_epoch;
      ghost var new_set := es.prev_req_set + es.cur_req_set;
      var new_map := es.prev_req_map + es.cur_req_map;
      prev_req_set.AddSet(cur_req_set);
      cur_req_set.RemoveAll();
      new_set := BoundCRequestHeaders(new_seq, new_set, es.constants.all.params.max_integer_val, prev_req_set);
      new_map := BoundCRequestMap(new_seq, new_map, es.constants.all.params.max_integer_val);

      es' := es.(current_view := CComputeSuccessorView(es.current_view, es.constants.all), current_view_suspectors := {}, epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := [],
            cur_req_set := {}, /** Manually Added for I1 */
            prev_req_set := new_set,
            cur_req_map := map[],
            prev_req_map := new_map); /** Manually Added for I1 */
      assert es'.requests_received_prev_epochs + es'.requests_received_this_epoch == es'.requests_received_prev_epochs;
      assert es'.prev_req_map + es'.cur_req_map == es'.prev_req_map;
      assert ReqMapMatch(CBoundRequestSequence(new_seq, es.constants.all.params.max_integer_val), new_map);
      assert es'.requests_received_prev_epochs == CBoundRequestSequence(new_seq, es.constants.all.params.max_integer_val);
      assert es'.prev_req_map == new_map;
      assert ReqMapMatch(es'.requests_received_prev_epochs, es'.prev_req_map);
      assert ReqMapMatch(es'.requests_received_prev_epochs + es'.requests_received_this_epoch, es'.prev_req_map + es'.cur_req_map);
      assert CElectionStateIsAbstractable(es');
      // lemma_ElectionStateCheckForQuorumOfViewSuspicions(es, es', clock);
      //   t1; 
      // t1; 		
        // t1
		}
	}


//   /** 16 + 3 */
// 	function method CElectionStateReflectReceivedRequest(es: CElectionState, req: CRequest) : CElectionState 
// 		requires CElectionStateIsValid(es)
// 		requires CRequestIsValid(req)
// 		ensures var es' := CElectionStateReflectReceivedRequest(es, req); CElectionStateIsValid(es') && ElectionStateReflectReceivedRequest(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestToRequest(req))
// 	{
// 		var t1 := 
//     if (exists earlier_req :: earlier_req in es.requests_received_prev_epochs && CRequestsMatch(earlier_req, req)) then 
//       var t1 := es; 
//       t1 
//     else 
//       var t1 := 
//       if (exists earlier_req :: earlier_req in es.requests_received_this_epoch && CRequestsMatch(earlier_req, req)) then 
//         var t1 := es; 
//         t1 
//       else 
//         var t1 := es.(requests_received_this_epoch := CBoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val)); 
//         t1; 
//       t1; 		
// 		t1
// 	}

  /** 7 + 5 */
  function method CRemoveExecutedRequestBatch(reqs: seq<CRequest>, batch: CRequestBatch) : seq<CRequest> 
		requires (forall i :: i in reqs ==> CRequestIsValid(i))
		requires CRequestBatchIsValid(batch)
		decreases |batch|
    ensures (forall i :: i in CRemoveExecutedRequestBatch(reqs, batch) ==> i.CRequest? && CRequestIsValid(i))
    ensures AbstractifySeq(CRemoveExecutedRequestBatch(reqs, batch), AbstractifyCRequestToRequest) == RemoveExecutedRequestBatch(AbstractifySeq(reqs, AbstractifyCRequestToRequest), AbstractifyCRequestBatchToRequestBatch(batch))
	{
		if |batch| == 0 then 
			reqs 
		else 
			CRemoveExecutedRequestBatch(CRemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), batch[1..])
	}

//   /** 5 + 3 */
// 	function method CElectionStateReflectExecutedRequestBatch(es: CElectionState, batch: CRequestBatch) : CElectionState 
// 		requires CElectionStateIsValid(es)
// 		requires CRequestBatchIsValid(batch)
// 		ensures var es' := CElectionStateReflectExecutedRequestBatch(es, batch); CElectionStateIsValid(es') && ElectionStateReflectExecutedRequestBatch(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestBatchToRequestBatch(batch))
// 	{
// 		var t1 := es.(requests_received_prev_epochs := CRemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch), requests_received_this_epoch := CRemoveExecutedRequestBatch(es.requests_received_this_epoch, batch)); 		
// 		t1
// 	}

  /************************** AutoMan Translation End ************************/


  /************************** Manually Optimization for I1 ********************/
  /** 1 + 0 */
  datatype CRequestHeader = CRequestHeader(client:EndPoint, seqno:int)

  method CCheckRequestValidInReqSeq_I1(m: map<CRequestHeader, CAppMessage>, ghost s:seq<CRequest>, r: CRequest) returns (b:bool)
    requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CRequestIsValid(r)
    requires ReqMapMatch(s, m)
		ensures  
        var cr := CCheckRequestValidInReqSeq(s, r); 
        b == cr
	{
    var header := CRequestHeader(r.client, r.seqno);

    if header !in m {
      b := false;
    } 
    else 
    {
      if m[header] != r.request {
        b := false;
      } 
      else 
      {
        b := true;
      }
    }
    lemma_CCheckRequestValidInReqSeq(m, s, r);
	}
          
  
  lemma lemma_CCheckRequestValidInReqSeq(m: map<CRequestHeader, CAppMessage>, s:seq<CRequest>, r: CRequest)
    requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CRequestIsValid(r)
    requires ReqMapMatch(s, m)
    ensures
          CCheckRequestValidInReqSeq(s, r) ==
          (CRequestHeader(r.client, r.seqno) in m && m[CRequestHeader(r.client, r.seqno)] == r.request)
  {
    if CCheckRequestValidInReqSeq(s, r) {
      var i :| i in s && CRequestsMatch(i, r) && i.request == r.request;
      assert CRequestHeader(i.client, i.seqno) in m;
      assert m[CRequestHeader(i.client, i.seqno)] == i.request;
      assert CRequestHeader(r.client, r.seqno) in m;
      assert m[CRequestHeader(r.client, r.seqno)] == r.request;
    }

    lemma_ReqMapMatch(s, m);
    if CRequestHeader(r.client, r.seqno) in m && m[CRequestHeader(r.client, r.seqno)] == r.request {
      var i :| i in s && CRequestHeader(i.client, i.seqno) == CRequestHeader(r.client, r.seqno);
      assert i.request == r.request;
      assert CCheckRequestValidInReqSeq(s, r);
    }
  }

  method CCheckRequestValid_I1(s: CElectionState, r: CRequest) returns (b:bool) 
		requires CElectionStateIsValid(s)
		requires CRequestIsValid(r)
		ensures var lr := CheckRequestValid(AbstractifyCElectionStateToElectionState(s), AbstractifyCRequestToRequest(r));
            b == lr
    ensures var r := CCheckRequestValid(s, r);
            b == r
	{
    var b1 := CCheckRequestValidInReqSeq_I1(s.cur_req_map, s.requests_received_this_epoch, r);
    if b1 {
      b := b1;
    } 
    else {
      var b2 := CCheckRequestValidInReqSeq_I1(s.prev_req_map, s.requests_received_prev_epochs, r);
      b := b2;
    }
	}

  method BoundCRequestMap(s:seq<CRequest>, m:map<CRequestHeader, CAppMessage>, lengthBound:CUpperBound) returns (new_map : map<CRequestHeader, CAppMessage>)
    requires SeqIsValid(s, CRequestIsValid)
    requires SeqIsAbstractable(s, AbstractifyCRequestToRequest)
    requires ReqMapMatch(s, m)
    ensures ReqMapMatch(CBoundRequestSequence(s, lengthBound), new_map)
    ensures forall r :: r in new_map ==> r in m
  {
    var i := 0;
    if lengthBound.CUpperBoundFinite? && 0 <= lengthBound.n < |s| {
        new_map := map[];
        while i < lengthBound.n
          invariant 0 <= i <= lengthBound.n;
          invariant ReqMapMatch(s[..i], new_map)
          invariant forall h :: h in new_map ==> h in m
        {
          var new_header := CRequestHeader(s[i].client, s[i].seqno);
          if new_header in new_map {
            var j := FindMatchingRequestForReqMap(s[..i], new_map, new_header);
            assert CRequestsMatch(s[j], s[i]);
            assert false;
          }
          assert new_header !in new_map;
          new_map := new_map[new_header := s[i].request];
          i := i + 1;
        }
    }
    else
    {
      new_map := m;
    }
  }


  /** 13 */
  method BoundCRequestHeaders(s:seq<CRequest>, ghost headers:set<CRequestHeader>, lengthBound:CUpperBound, cur_req_set:MutableSet<CRequestHeader>)
    returns (ghost new_headers:set<CRequestHeader>)
    // requires |s| < 0x1_0000_0000_0000_0000
    requires SeqIsValid(s, CRequestIsValid)
    requires SeqIsAbstractable(s, AbstractifyCRequestToRequest)
    requires HeadersMatch(s, headers)
    requires MutableSet.SetOf(cur_req_set) == headers
    // requires lengthBound.CUpperBoundInfinite?
    // requires lengthBound.CUpperBoundFinite? ==> |s| > lengthBound.n
    modifies cur_req_set
    ensures  HeadersMatch(CBoundRequestSequence(s, lengthBound), new_headers)
    ensures  forall h :: h in new_headers ==> h in headers
    ensures MutableSet.SetOf(cur_req_set) == new_headers
  {
    var i := 0;
    
    if lengthBound.CUpperBoundFinite? && 0 <= lengthBound.n < |s| {
        new_headers := {};
        cur_req_set.RemoveAll();
        while i < lengthBound.n
          invariant 0 <= i <= lengthBound.n;
          invariant HeadersMatch(s[..i], new_headers)
          invariant forall h :: h in new_headers ==> h in headers
          invariant MutableSet.SetOf(cur_req_set) == new_headers
      {
        var new_header := CRequestHeader(s[i].client, s[i].seqno);
        if new_header in new_headers {
          var j := FindMatchingRequest(s[..i], new_headers, new_header); 
          // reveal_CRequestsMatch();
          assert CRequestsMatch(s[j], s[i]);
          assert false;
        }
        new_headers := new_headers + { new_header };
        cur_req_set.Add(new_header);
        i := i + 1;
      }

      // reveal_CBoundRequestSequence();
      assert HeadersMatch(CBoundRequestSequence(s, lengthBound), new_headers);
      assert MutableSet.SetOf(cur_req_set) == new_headers;
      
    } else {
      new_headers := headers;
      assert CBoundRequestSequence(s, lengthBound) == s;
      assert HeadersMatch(s, headers);
      assert HeadersMatch(CBoundRequestSequence(s, lengthBound), new_headers);
      assert MutableSet.SetOf(cur_req_set) == headers;
      assert MutableSet.SetOf(cur_req_set) == new_headers;
    }
  }

  /** 11 + 27 */
  method FindEarlierRequests(ces:CElectionState, target:CRequest, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (b:bool)
    requires CElectionStateIsValid(ces)
    requires CRequestIsAbstractable(target)
    requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
    ensures  b == exists earlier_req :: (earlier_req in ces.requests_received_prev_epochs 
                                          || earlier_req in ces.requests_received_this_epoch)
                                      && CRequestsMatch(earlier_req, target)
    ensures  b == exists earlier_req :: (earlier_req in AbstractifySeq(ces.requests_received_prev_epochs, AbstractifyCRequestToRequest) 
                                          || earlier_req in AbstractifySeq(ces.requests_received_this_epoch, AbstractifyCRequestToRequest))
                                      && RequestsMatch(earlier_req, AbstractifyCRequestToRequest(target))
  {
    var header := CRequestHeader(target.client, target.seqno);
    var b1 := cur_req_set.Contains(header);
    if b1 {
      b := true;
    } else {
      var b2 := prev_req_set.Contains(header);
      b := b2;
    }
    assert b == (header in ces.cur_req_set) || (header in ces.prev_req_set);
    lemma_CRequestsMatch();
    if b {
      ghost var requests := ces.requests_received_prev_epochs + ces.requests_received_this_epoch;
      ghost var i := FindMatchingRequest(requests, ces.prev_req_set + ces.cur_req_set, header); 
      // Lots of OBSERVE below to satisfy the existential in the ensures clause
      if i < |ces.requests_received_prev_epochs| {
        assert requests[i] == ces.requests_received_prev_epochs[i];
        ghost var r_req := AbstractifyCRequestToRequest(ces.requests_received_prev_epochs[i]);
        assert r_req in AbstractifySeq(ces.requests_received_prev_epochs, AbstractifyCRequestToRequest);
        assert RequestsMatch(r_req, AbstractifyCRequestToRequest(target));
      } else {
        assert requests[i] == ces.requests_received_this_epoch[i - |ces.requests_received_prev_epochs|];
        ghost var r_req := AbstractifyCRequestToRequest(ces.requests_received_this_epoch[i - |ces.requests_received_prev_epochs|]);
        assert r_req in AbstractifySeq(ces.requests_received_this_epoch, AbstractifyCRequestToRequest);
        assert RequestsMatch(r_req, AbstractifyCRequestToRequest(target));
      }
    }
  }

  method{:timeLimitMultiplier 1} CRemoveAllSatisfiedRequestsInSequence_I1(
    requests:seq<CRequest>,
    ghost headers:set<CRequestHeader>,
    reqmap:map<CRequestHeader, CAppMessage>,
    cur_req_set:MutableSet<CRequestHeader>,
    r:CRequest
    ) returns (
    requests':seq<CRequest>,
    ghost headers':set<CRequestHeader>,
    reqmap':map<CRequestHeader, CAppMessage>
    )
    requires SeqIsValid(requests,CRequestIsValid)
    requires CRequestIsValid(r)
    requires HeadersMatch(requests, headers)
    requires ReqMapMatch(requests, reqmap)
    requires MutableSet.SetOf(cur_req_set) == headers
    modifies cur_req_set
    ensures  requests' == CRemoveAllSatisfiedRequestsInSequence(requests, r) /** Refines I0 */
    ensures  HeadersMatch(requests', headers')
    ensures  ReqMapMatch(requests', reqmap')
    ensures  MutableSet.SetOf(cur_req_set) == headers'
  {
    var i := 0;
    var len := |requests|;
    ghost var removed_headers:set<CRequestHeader> := {};
    ghost var removed_map:map<CRequestHeader, CAppMessage> := map[];
    headers' := {};
    requests' := [];
    reqmap' := map[];
    i := 0;

    lemma_EmptyHeadersMatch(requests', headers');
    assert ReqMapMatch(requests', reqmap');

    while i < len
      invariant 0 <= i <= len
      invariant SeqIsValid(requests',CRequestIsValid)
      invariant HeadersMatch(requests', headers')
      invariant ReqMapMatch(requests', reqmap')
      invariant forall r' :: r' in requests' ==> r' in requests[..i]
      invariant requests' == CRemoveAllSatisfiedRequestsInSequence(requests[..i], r)
      invariant MutableSet.SetOf(cur_req_set) == headers - removed_headers
      invariant headers' + removed_headers == HeadersFromPrefix(requests, i as int)
      // invariant |reqmap' + removed_map| == i
      // invariant forall j :: 0 <= j < i ==> ExtractHeader(requests[j]) in reqmap' + removed_map
      invariant removed_headers * headers' == {}
      // invariant forall i :: i in removed_map ==> i !in reqmap'
      // invariant forall i :: i in reqmap' ==> i !in removed_map
    {
      ghost var old_requests' := requests';
      ghost var old_headers' := headers';
      ghost var old_map' := reqmap';

      lemma_RemoveAllSatisfiedCRequestsInSequenceUpdate(requests, r, i as int);

      var h := CRequestHeader(requests[i].client, requests[i].seqno);
      if h in removed_headers || h in headers'
      {
        var j :| 0 <= j < i && h == CRequestHeader(requests[j].client, requests[j].seqno);
        assert CRequestsMatch(requests[j], requests[i]);
        assert false;
      }

      // if h in removed_map || h in reqmap'
      // {
      //   var j :| 0 <= j < i && h == CRequestHeader(requests[j].client, requests[j].seqno);
      //   assert CRequestsMatch(requests[j], requests[i]);
      //   assert false;
      // }
          
          
      if CRequestSatisfiedBy(requests[i], r) {
        cur_req_set.Remove(h);
        removed_headers := removed_headers + {h};
        removed_map := removed_map[h := r.request];
      }
      else 
      {
        headers' := headers' + {h};
        requests' := requests' + [requests[i]];
        reqmap' := reqmap'[h := requests[i].request];
        lemma_AddingOneHeaderPreservesMatch(old_requests', old_headers', requests[i], requests', headers');
        assert requests' == old_requests' + [requests[i]];
        assert reqmap' == old_map'[CRequestHeader(requests[i].client, requests[i].seqno) := requests[i].request];
        assert ReqMapMatch(old_requests', old_map');
        lemma_AddingOneHeaderToReqMapPreservesMatch(old_requests', old_map', requests[i], requests', reqmap');
      }

      assert ReqMapMatch(requests', reqmap');
      lemma_HeadersFromPrefixIncrease(requests, i as int);
      i := i + 1;
    }
    assert requests[..i] == requests;
    lemma_HeadersMatchImpliesHeadersFromPrefix(requests, headers);
    // lemma_ReqMapMatch(requests', reqmap');
  }


  /** 15 + 31 */
  method {:opaque} CElectionStateReflectReceivedRequest_I1(ces:CElectionState, creq:CRequest, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (ces':CElectionState)
    requires CElectionStateIsValid(ces)
    requires CRequestIsValid(creq)
    requires prev_req_set != cur_req_set
    requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
    modifies cur_req_set
    ensures CElectionStateIsValid(ces')
    ensures  ElectionStateReflectReceivedRequest(AbstractifyCElectionStateToElectionState(ces), 
              AbstractifyCElectionStateToElectionState(ces'), 
              AbstractifyCRequestToRequest(creq)) 
    ensures MutableSet.SetOf(cur_req_set) == ces'.cur_req_set
    ensures MutableSet.SetOf(prev_req_set) == ces'.prev_req_set
  {
    ghost var req := AbstractifyCRequestToRequest(creq);
    ghost var es  := AbstractifyCElectionStateToElectionState(ces);
    ghost var es':ElectionState;

    var find_earlier := FindEarlierRequests(ces, creq, cur_req_set, prev_req_set);

    if find_earlier {
      ces' := ces;
    } else {
      es' := es.(requests_received_this_epoch := BoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val));
      var new_seq := ces.requests_received_this_epoch + [creq];
      var header := CRequestHeader(creq.client, creq.seqno);
      ghost var new_set := ces.cur_req_set + { header };
      var new_map := ces.cur_req_map[header:=creq.request];

      cur_req_set.Add(header);
      lemma_HeadersMatchAddition(ces.requests_received_this_epoch, ces.cur_req_set, creq);
      assert HeadersMatch(new_seq, new_set);

      lemma_ReqMapMatchAddition(ces.requests_received_this_epoch, ces.cur_req_map, creq);
      assert ReqMapMatch(new_seq, new_map);

      var bounded_seq := CBoundRequestSequence(new_seq, ces.constants.all.params.max_integer_val);
      assert MutableSet.SetOf(cur_req_set) == new_set;
      new_set := BoundCRequestHeaders(new_seq, new_set, ces.constants.all.params.max_integer_val, cur_req_set);

      
      new_map := BoundCRequestMap(new_seq, new_map, ces.constants.all.params.max_integer_val);
      assert ReqMapMatch(bounded_seq, new_map);
      
      ces' := ces.(
        requests_received_this_epoch := bounded_seq,
        cur_req_set := new_set,
        cur_req_map := new_map
      );

      // assert forall h :: h in ces.prev_req_map ==> h !in ces.cur_req_map;
      assert ReqMapMatch(ces'.requests_received_this_epoch, ces'.cur_req_map);
      assert ReqMapMatch(ces'.requests_received_prev_epochs, ces'.prev_req_map);
      // assert forall h :: h in ces.prev_req_map ==> h !in new_map;
      // assert forall h :: h in new_map ==> h !in ces.prev_req_map;
      lemma_AddNewReqPreservesReqMapMatches(ces.requests_received_prev_epochs, ces.prev_req_map,
                                            ces.requests_received_this_epoch,  ces.cur_req_map,
                                            ces.requests_received_prev_epochs, ces.prev_req_map,
                                            bounded_seq, new_map,
                                            creq);
      assert ReqMapMatch(ces'.requests_received_prev_epochs + ces'.requests_received_this_epoch, ces'.prev_req_map + ces'.cur_req_map);

      lemma_AddNewReqPreservesHeaderMatches(ces.requests_received_prev_epochs, ces.prev_req_set,
                                            ces.requests_received_this_epoch,  ces.cur_req_set,
                                            ces.requests_received_prev_epochs, ces.prev_req_set,
                                            bounded_seq, new_set,
                                            creq);
      lemma_seq_concat(ces.requests_received_this_epoch, [creq], AbstractifyCRequestToRequest);
      lemma_BoundCRequestSequence(bounded_seq, ces.constants.all.params.max_integer_val);

      assert {:split_here} true;
    }
  }

  /** 15 + 49 */
  method {:timeLimitMultiplier 3} CElectionStateReflectExecutedRequestBatch_I1(ces:CElectionState, creqb:CRequestBatch, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (ces':CElectionState)
    requires CElectionStateIsValid(ces)
    requires CRequestBatchIsValid(creqb)
    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  CElectionStateIsValid(ces')
    ensures  ElectionStateReflectExecutedRequestBatch(AbstractifyCElectionStateToElectionState(ces), AbstractifyCElectionStateToElectionState(ces'), AbstractifyCRequestBatchToRequestBatch(creqb))
    ensures MutableSet.SetOf(cur_req_set) == ces'.cur_req_set
    ensures MutableSet.SetOf(prev_req_set) == ces'.prev_req_set
    decreases |creqb|
  {
    ghost var es  := AbstractifyCElectionStateToElectionState(ces);
    var i:uint64 := 0;
    assert AbstractifyCRequestBatchToRequestBatch(creqb[..i]) == [];
    var tempces' := ces;

    while i < |creqb| as uint64
      invariant 0 <= i as int <= |creqb|
      invariant CElectionStateIsAbstractable(tempces')
      invariant CElectionStateIsValid(tempces')
      invariant ElectionStateReflectExecutedRequestBatch(es, AbstractifyCElectionStateToElectionState(tempces'), AbstractifyCRequestBatchToRequestBatch(creqb[..i]))
      invariant MutableSet.SetOf(cur_req_set) == tempces'.cur_req_set
      invariant MutableSet.SetOf(prev_req_set) == tempces'.prev_req_set
    { 
      var creq := creqb[i];

      ghost var req := AbstractifyCRequestToRequest(creq);
      ghost var es':ElectionState := AbstractifyCElectionStateToElectionState(tempces');
        
      lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(tempces'.requests_received_prev_epochs, creq);
      lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(tempces'.requests_received_this_epoch, creq);

      assert ElectionStateReflectExecutedRequestBatch(es, AbstractifyCElectionStateToElectionState(tempces'), AbstractifyCRequestBatchToRequestBatch(creqb[..i]));
      ghost var es'' := es'.(requests_received_prev_epochs := RemoveAllSatisfiedRequestsInSequence(es'.requests_received_prev_epochs, req),
                            requests_received_this_epoch := RemoveAllSatisfiedRequestsInSequence(es'.requests_received_this_epoch, req));

      var prevEpoch;
      ghost var prevEpochSet;
      var prevEpochMap;
      prevEpoch, prevEpochSet, prevEpochMap := CRemoveAllSatisfiedRequestsInSequence_I1(tempces'.requests_received_prev_epochs, tempces'.prev_req_set, tempces'.prev_req_map, prev_req_set, creq);
      var thisEpoch; 
      ghost var thisEpochSet;
      var thisEpochMap;
      thisEpoch, thisEpochSet, thisEpochMap := CRemoveAllSatisfiedRequestsInSequence_I1(tempces'.requests_received_this_epoch, tempces'.cur_req_set, tempces'.cur_req_map, cur_req_set, creq);

      // var prevEpoch;
      // ghost var prevEpochSet;
      // prevEpoch, prevEpochSet := CRemoveAllSatisfiedRequestsInSequence_I1(tempces'.requests_received_prev_epochs, tempces'.prev_req_set, prev_req_set, creq);
      // var thisEpoch; 
      // ghost var thisEpochSet;
      // thisEpoch, thisEpochSet := CRemoveAllSatisfiedRequestsInSequence_I1(tempces'.requests_received_this_epoch, tempces'.cur_req_set, cur_req_set, creq);

      lemma_RemoveAllSatisfiedPreservesHeaderMatches(tempces'.requests_received_prev_epochs, tempces'.prev_req_set,
                                                    tempces'.requests_received_this_epoch, tempces'.cur_req_set,
                                                    prevEpoch, prevEpochSet,
                                                    thisEpoch, thisEpochSet,
                                                    creq);

      lemma_RemoveAllSatisfiedPreservesReqMapMatches(tempces'.requests_received_prev_epochs, tempces'.prev_req_map,
                                                    tempces'.requests_received_this_epoch, tempces'.cur_req_map,
                                                    prevEpoch, prevEpochMap,
                                                    thisEpoch, thisEpochMap,
                                                    creq);
      

      tempces' := tempces'.(requests_received_prev_epochs := prevEpoch,
                            requests_received_this_epoch := thisEpoch,
                            cur_req_set := thisEpochSet,
                            prev_req_set := prevEpochSet
                            ,
                            cur_req_map := thisEpochMap,
                            prev_req_map := prevEpochMap
                            );

      // lemma_ReqMapMatch(tempces'.requests_received_prev_epochs + tempces'.requests_received_this_epoch, tempces'.prev_req_map + tempces'.cur_req_map);
      // assume |tempces'.requests_received_this_epoch| == |tempces'.cur_req_map|;
      assert ReqMapMatch(tempces'.requests_received_prev_epochs + tempces'.requests_received_this_epoch, tempces'.prev_req_map + tempces'.cur_req_map);
      assert CElectionStateIsAbstractable(tempces');

      assert {:split_here} true;
      assert AbstractifyCRequestBatchToRequestBatch(creqb[..i]) == AbstractifyCRequestBatchToRequestBatch(creqb)[..i];
      assert AbstractifyCRequestBatchToRequestBatch(creqb[..i+1]) == AbstractifyCRequestBatchToRequestBatch(creqb)[..i+1];
      lemma_SequenceRemoveAllSatisfied(es.requests_received_prev_epochs, AbstractifyCRequestBatchToRequestBatch(creqb), i as int, es'.requests_received_prev_epochs, es''.requests_received_prev_epochs);
      lemma_SequenceRemoveAllSatisfied(es.requests_received_this_epoch, AbstractifyCRequestBatchToRequestBatch(creqb), i as int, es'.requests_received_this_epoch, es''.requests_received_this_epoch);
      i := i + 1;
    }
    assert creqb[..i] == creqb;
    ces' := tempces';
  }

   /** 0 + 7 */
  predicate HeadersMatch(requests:seq<CRequest>, headers:set<CRequestHeader>)
    requires SeqIsValid(requests, CRequestIsValid) 
  {
    &&  |requests| == |headers|
    && (forall r :: r in requests ==> CRequestHeader(r.client, r.seqno) in headers)
    && (forall i,j {:trigger CRequestsMatch(requests[i], requests[j])} :: 0 <= i < j < |requests| && CRequestsMatch(requests[i], requests[j]) ==> i == j)
  }

  /** 0 + 7 */
  predicate ReqMapMatch(requests:seq<CRequest>, reqmap:map<CRequestHeader, CAppMessage>)
    requires SeqIsValid(requests, CRequestIsValid) 
  {
    &&  |requests| == |reqmap|
    && (forall i,j {:trigger CRequestsMatch(requests[i], requests[j])} :: 0 <= i < j < |requests| && CRequestsMatch(requests[i], requests[j]) ==> i == j)
    && (forall r :: r in requests ==> CRequestHeader(r.client, r.seqno) in reqmap && r.request == reqmap[CRequestHeader(r.client, r.seqno)])
    // && (forall h :: h in reqmap ==> exists r :: r in requests && CRequestHeader(r.client, r.seqno) == h &&  r.request == reqmap[h])
  }

  lemma lemma_test<A>(s1:set<A>, s2:set<A>)
    requires |s1| == |s2|
    requires forall i :: i in s1 ==> i in s2
    ensures forall i :: i in s2 ==> i in s1
  {
     forall i | i in s2
      ensures i in s1
    {
        if i !in s1 {
            assert exists j :: j in s2 && j !in s1;
            assert |s2 - s1| > 0; 

         
            assert |s1| == |s2|;
            assert |s1| < |s2|; 
            assert false;       
        }
        assert i in s1;
    }
  }

  lemma lemma_ReqMapMatch(requests:seq<CRequest>, reqmap:map<CRequestHeader, CAppMessage>)
    requires SeqIsValid(requests, CRequestIsValid) 
    requires ReqMapMatch(requests, reqmap)
    ensures (forall h :: h in reqmap ==> exists r :: r in requests && CRequestHeader(r.client, r.seqno) == h && r.request == reqmap[h])
  {
    var header_seq := [];
    var i := 0;
    while i < |requests|
      invariant 0 <= i <= |requests|
      invariant |header_seq| == i
      invariant forall j :: 0 <= j < i ==> header_seq[j] == ExtractHeader(requests[j])
    {
      header_seq := header_seq + [ExtractHeader(requests[i])];
      i := i + 1;
    }

    assert |header_seq| == |reqmap|;

    forall h | h in header_seq
        ensures h in reqmap.Keys
    {
        var i :| 0 <= i < |requests| && header_seq[i] == h;
        assert CRequestHeader(requests[i].client, requests[i].seqno) == h;
        assert h in reqmap; // 由 ReqMapMatch 保证
    }

    forall i', j' | 0 <= i' < |header_seq| && 0 <= j' < |header_seq| && header_seq[i'] == header_seq[j']
      ensures i' == j'
    {
      assert header_seq[i'] == ExtractHeader(requests[i']);
      assert header_seq[j'] == ExtractHeader(requests[j']);
      if i' < j' {
        assert CRequestsMatch(requests[i'], requests[j']);  // OBSERVE
      } else if j' < i' {
        assert CRequestsMatch(requests[j'], requests[i']);  // OBSERVE
      }
    }
    forall ensures SeqIsUnique(header_seq)
    {
      reveal SeqIsUnique();
    }

    assert SeqIsUnique(header_seq);
    var header_set := UniqueSeqToSet(header_seq);
    lemma_seqs_set_cardinality(header_seq, header_set);
    assert |header_seq| == |header_set|;
    assert |header_set| == |reqmap.Keys|;

    assert forall h :: h in header_set ==> h in reqmap.Keys;

    lemma_test(header_set, reqmap.Keys);

    assert forall h :: h in reqmap.Keys ==> h in header_set;
  
    forall h | h in reqmap.Keys
        ensures h in header_seq
    {
        var r :| r in requests && CRequestHeader(r.client, r.seqno) == h;
        assert r in requests;
    }

  }


  /** 0 + 8 */
  lemma lemma_EmptyHeadersMatch(
    s:seq<CRequest>,
    headers:set<CRequestHeader>
    )
    requires s == []
    requires headers == {}
    ensures HeadersMatch(s, headers)
  {
  }

  /** 0 + 16 */
  lemma lemma_SequenceRemoveAllSatisfied(rseq:seq<Request>, batch:RequestBatch, i:int, rseq':seq<Request>, rseq'':seq<Request>)
    requires 0 <= i < |batch|
    requires rseq' == RemoveExecutedRequestBatch(rseq, batch[..i])
    requires rseq'' == RemoveAllSatisfiedRequestsInSequence(rseq', batch[i])
    ensures rseq'' == RemoveExecutedRequestBatch(rseq, batch[..i+1])
    decreases i
  {
    if i > 0 {
      assert batch[1..][..i-1] == batch[1..i]; 
      assert batch[1..][..i] == batch[1..i+1]; 
      var rseqalt := RemoveAllSatisfiedRequestsInSequence(rseq, batch[0]);
      var rseqalt' := RemoveExecutedRequestBatch(rseqalt, batch[1..i]);
      var rseqalt'' := RemoveAllSatisfiedRequestsInSequence(rseqalt', batch[i]);

      lemma_SequenceRemoveAllSatisfied(rseqalt, batch[1..], i-1, rseqalt', rseqalt''); 
    }
  }

  /** 0 + 29 */
  lemma lemma_AddingOneHeaderPreservesMatch(
    s:seq<CRequest>,
    headers:set<CRequestHeader>,
    r:CRequest,
    s':seq<CRequest>,
    headers':set<CRequestHeader>
    )
    requires SeqIsValid(s,CRequestIsValid)
    requires CRequestIsValid(r)
    requires s' == s + [r]
    requires headers' == headers + { CRequestHeader(r.client, r.seqno) }
    requires HeadersMatch(s, headers)
    requires forall r' :: r' in s ==> !CRequestsMatch(r', r)
    ensures  HeadersMatch(s', headers')
  {
    var new_header := CRequestHeader(r.client, r.seqno);
    if new_header in headers
    {
      var i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(s, headers, new_header);
      assert CRequestsMatch(s[i], r);
      assert false;
    }
    calc {
      |s'|;
      |s| + 1;
      |headers| + 1;
      |headers'|;
    }
    assert forall r' :: r' in s' ==> CRequestHeader(r'.client, r'.seqno) in headers';
  }

  lemma lemma_AddingOneHeaderToReqMapPreservesMatch(
    s:seq<CRequest>,
    reqmap:map<CRequestHeader, CAppMessage>,
    r:CRequest,
    s':seq<CRequest>,
    reqmap':map<CRequestHeader, CAppMessage>
    )
    requires SeqIsValid(s,CRequestIsValid)
    requires CRequestIsValid(r)
    requires s' == s + [r]
    requires reqmap' == reqmap[CRequestHeader(r.client, r.seqno) := r.request]
    requires ReqMapMatch(s, reqmap)
    requires forall r' :: r' in s ==> !CRequestsMatch(r', r)
    ensures  ReqMapMatch(s', reqmap')
  {
    var new_header := CRequestHeader(r.client, r.seqno);
    if new_header in reqmap
    {
      var i := lemma_ReqMapMatchImpliesEveryHeaderHasACorrespondingEntry(s, reqmap, new_header);
      assert CRequestsMatch(s[i], r);
      assert false;
    }
    // calc {
    //   |s'|;
    //   |s| + 1;
    //   |headers| + 1;
    //   |headers'|;
    // }
    assert forall r' :: r' in s' ==> CRequestHeader(r'.client, r'.seqno) in reqmap';
  }

  /** 0 + 41 */
  lemma lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(
    requests:seq<CRequest>,
    headers:set<CRequestHeader>,
    header:CRequestHeader
    ) returns (
    i:int
    )
    requires SeqIsValid(requests, CRequestIsValid)
    requires HeadersMatch(requests, headers)
    requires header in headers
    ensures  0 <= i < |requests|
    ensures  header.client == requests[i].client
    ensures  header.seqno == requests[i].seqno
  {
    if |requests| == 0 {
      return;
    }

    var num_requests := |requests|;
    var last_header := CRequestHeader(requests[num_requests-1].client, requests[num_requests-1].seqno);
    assert last_header in headers;

    if header == last_header
    {
      i := num_requests - 1;
      return;
    }

    var requests' := requests[..num_requests-1];
    var headers' := headers - { last_header };

    forall r' | r' in requests'
      ensures CRequestHeader(r'.client, r'.seqno) in headers'
    {
      var j :| 0 <= j < |requests|-1 && r' == requests[j];
      var k := |requests| - 1;
      // reveal_CRequestsMatch();
      assert !CRequestsMatch(requests[j], requests[k]);
    }

    i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests[..num_requests - 1], headers - { last_header }, header);
  }

  lemma lemma_ReqMapMatchImpliesEveryHeaderHasACorrespondingEntry(
    requests:seq<CRequest>,
    reqmap:map<CRequestHeader, CAppMessage>,
    header:CRequestHeader
    ) returns (
    i:int
    )
    requires SeqIsValid(requests, CRequestIsValid)
    requires ReqMapMatch(requests, reqmap)
    requires header in reqmap
    ensures  0 <= i < |requests|
    ensures  header.client == requests[i].client
    ensures  header.seqno == requests[i].seqno
  {
    if |requests| == 0 {
      return;
    }

    var num_requests := |requests|;
    var last_header := CRequestHeader(requests[num_requests-1].client, requests[num_requests-1].seqno);
    assert last_header in reqmap;

    if header == last_header
    {
      i := num_requests - 1;
      return;
    }

    var requests' := requests[..num_requests-1];
    var reqmap' := RemoveElt(reqmap, last_header);

    forall r' | r' in requests'
      ensures CRequestHeader(r'.client, r'.seqno) in reqmap'
    {
      var j :| 0 <= j < |requests|-1 && r' == requests[j];
      var k := |requests| - 1;
      // reveal_CRequestsMatch();
      assert !CRequestsMatch(requests[j], requests[k]);
    }

    i := lemma_ReqMapMatchImpliesEveryHeaderHasACorrespondingEntry(requests', reqmap', header);
  }

  /** 0 + 5 */
  lemma lemma_HeadersFromPrefixIncrease(s:seq<CRequest>, i:int)
    requires 0 <= i
    requires i+1 <= |s|
    ensures  HeadersFromPrefix(s, i+1) == HeadersFromPrefix(s, i) + { CRequestHeader(s[i].client, s[i].seqno) }
  {
  }

  /** 0 + 18 */
  lemma lemma_HeadersMatchImpliesHeadersFromPrefix(requests:seq<CRequest>, headers:set<CRequestHeader>)
    requires SeqIsValid(requests,CRequestIsValid)
    requires HeadersMatch(requests, headers)
    ensures  headers == HeadersFromPrefix(requests, |requests|)
  {
    var headers' := HeadersFromPrefix(requests, |requests|);

    forall h | h in headers
      ensures h in headers'
    {
      var i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests, headers, h);
    }

    forall h | h in headers'
      ensures h in headers
    {
      var i :| 0 <= i < |requests| && h == CRequestHeader(requests[i].client, requests[i].seqno);
    }
  }

  /** 0 + 11 */
  function {:fuel 5,6} RemoveAllSatisfiedCRequestsInSequence(s:seq<CRequest>, r:CRequest):seq<CRequest>
    requires SeqIsValid(s, CRequestIsValid)
    requires CRequestIsValid(r)
    ensures  forall r' :: r' in RemoveAllSatisfiedCRequestsInSequence(s, r) ==> r' in s
  {
    if |s| == 0 then
      []
    else if CRequestSatisfiedBy(s[0], r) then
      RemoveAllSatisfiedCRequestsInSequence(s[1..], r)
    else
      [s[0]] + RemoveAllSatisfiedCRequestsInSequence(s[1..], r)
  }

  /** 0 + 10 */
  lemma lemma_RemoveAllSatisfiedCRequestsInSequenceUpdate(s:seq<CRequest>, r:CRequest, i:int)
    requires 0 <= i < |s|
    requires SeqIsValid(s,CRequestIsValid)
    requires CRequestIsValid(r)
    ensures  CRemoveAllSatisfiedRequestsInSequence(s[..i+1], r) == CRemoveAllSatisfiedRequestsInSequence(s[..i], r) + if CRequestSatisfiedBy(s[i], r) then [] else [s[i]]
  {
    var s' := s[..i+1];
    assert last(s') == s[i];
    assert all_but_last(s') == s[..i];
    lemma_RemoveAllSatisfiedCRequestsInSequenceAltEquivalent(s', r);
  }

  /** 0 + 13 */
  lemma lemma_RemoveAllSatisfiedCRequestsInSequenceAltEquivalent(s:seq<CRequest>, r:CRequest)
    requires SeqIsValid(s,CRequestIsValid)
    requires CRequestIsValid(r)
    ensures CRemoveAllSatisfiedRequestsInSequence(s, r) == RemoveAllSatisfiedCRequestsInSequenceAlt(s, r)
  {
    if |s| == 0 || |s| == 1 {
      return;
    }

    lemma_RemoveAllSatisfiedCRequestsInSequenceAltEquivalent(s[1..], r);
    lemma_RemoveAllSatisfiedCRequestsInSequenceAltEquivalent(all_but_last(s[1..]), r);
    assert all_but_last(s)[0] == s[0];
    assert all_but_last(s)[1..] == all_but_last(s[1..]);
  }

  /** 0 + 10 */
  function {:fuel 5,6} RemoveAllSatisfiedCRequestsInSequenceAlt(s:seq<CRequest>, r:CRequest):seq<CRequest>
    requires SeqIsValid(s,CRequestIsValid)
    requires CRequestIsValid(r)
  {
    if |s| == 0 then
      []
    else if CRequestSatisfiedBy(last(s), r) then
      CRemoveAllSatisfiedRequestsInSequence(all_but_last(s), r)
    else
      CRemoveAllSatisfiedRequestsInSequence(all_but_last(s), r) + [last(s)]
  }

  /** 0 + 5 */
  function HeadersFromPrefix(s:seq<CRequest>, i:int):set<CRequestHeader>
    requires 0 <= i <= |s|
  {
    set j | 0 <= j < i :: CRequestHeader(s[j].client, s[j].seqno)
  }

  /** 0 + 37 */
  lemma lemma_RemoveAllSatisfiedPreservesHeaderMatches(requests1:seq<CRequest>,  headers1:set<CRequestHeader>, 
                                                      requests2:seq<CRequest>,  headers2:set<CRequestHeader>,
                                                      requests1':seq<CRequest>, headers1':set<CRequestHeader>,
                                                      requests2':seq<CRequest>, headers2':set<CRequestHeader>,
                                                      r:CRequest)
    
    requires SeqIsValid(requests1, CRequestIsValid)
    requires SeqIsValid(requests2, CRequestIsValid)
    requires SeqIsValid(requests1', CRequestIsValid)
    requires SeqIsValid(requests2', CRequestIsValid)
    requires CRequestIsValid(r)
    requires HeadersMatch(requests1, headers1)
    requires HeadersMatch(requests2, headers2)
    requires HeadersMatch(requests1 + requests2, headers1 + headers2)
    requires HeadersMatch(requests1', headers1')
    requires HeadersMatch(requests2', headers2')
    requires requests1' == CRemoveAllSatisfiedRequestsInSequence(requests1, r)
    requires requests2' == CRemoveAllSatisfiedRequestsInSequence(requests2, r)
    ensures  HeadersMatch(requests1' + requests2', headers1' + headers2')
  {
    var requests3 := requests1 + requests2;
    var requests3' := requests1' + requests2';
    var headers3' := headers1' + headers2';

    lemma_RemoveAllSatisfiedCRequestsProducesHeaderSubset(requests1, headers1, requests1', headers1', r);
    lemma_RemoveAllSatisfiedCRequestsProducesHeaderSubset(requests2, headers2, requests2', headers2', r);

    forall h | h in headers1' && h in headers2'
      ensures false
    {
      assert h in headers1 && h in headers2;
      var i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests1, headers1, h);
      var j := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests2, headers2, h);
      assert CRequestsMatch(requests3[i], requests3[j + |requests1|]);
    }
    assert headers1' * headers2' == {};
    assert |requests3'| == |headers3'|;
  }

  lemma lemma_RemoveAllSatisfiedPreservesReqMapMatches(requests1:seq<CRequest>,  map1:map<CRequestHeader, CAppMessage>, 
                                                      requests2:seq<CRequest>,  map2:map<CRequestHeader, CAppMessage>,
                                                      requests1':seq<CRequest>, map1':map<CRequestHeader, CAppMessage>,
                                                      requests2':seq<CRequest>, map2':map<CRequestHeader, CAppMessage>,
                                                      r:CRequest)
    
    requires SeqIsValid(requests1, CRequestIsValid)
    requires SeqIsValid(requests2, CRequestIsValid)
    requires SeqIsValid(requests1', CRequestIsValid)
    requires SeqIsValid(requests2', CRequestIsValid)
    requires CRequestIsValid(r)
    requires ReqMapMatch(requests1, map1)
    requires ReqMapMatch(requests2, map2)
    requires ReqMapMatch(requests1 + requests2, map1 + map2)
    requires ReqMapMatch(requests1', map1')
    requires ReqMapMatch(requests2', map2')
    requires requests1' == CRemoveAllSatisfiedRequestsInSequence(requests1, r)
    requires requests2' == CRemoveAllSatisfiedRequestsInSequence(requests2, r)
    ensures  ReqMapMatch(requests1' + requests2', map1' + map2')
  {
    var requests3 := requests1 + requests2;
    var requests3' := requests1' + requests2';
    var map3' := map1' + map2';
    assert | requests1' | == |map1'|;
    assert |requests2'| == |map2'|;
    assert |requests3'| == |requests1'| + |requests2'|;

    lemma_RemoveAllSatisfiedCRequestsProducesReqMapSubset(requests1, map1, requests1', map1', r);
    lemma_RemoveAllSatisfiedCRequestsProducesReqMapSubset(requests2, map2, requests2', map2', r);

    forall h | h in map1' && h in map2'
      ensures false
    {
      assert h in map1 && h in map2;
      var i := lemma_ReqMapMatchImpliesEveryHeaderHasACorrespondingEntry(requests1, map1, h);
      var j := lemma_ReqMapMatchImpliesEveryHeaderHasACorrespondingEntry(requests2, map2, h);
      assert CRequestsMatch(requests3[i], requests3[j + |requests1|]);
    }
    assert forall i, j :: i in map1' && j in map2' ==> i != j;
    lemma_MapAdd(map1', map2', map3');
    assert |map3'| == |map1'| + |map2'|;
    assert |requests3'| == |map3'|;
    assert (forall i,j :: 0 <= i < j < |requests3'| && CRequestsMatch(requests3'[i], requests3'[j]) ==> i == j);
    assert forall r :: r in requests3' ==> CRequestHeader(r.client, r.seqno) in map3' && r.request == map3'[CRequestHeader(r.client, r.seqno)];
  }

  lemma lemma_MapAdd<K(!new), V(!new)>(m1:map<K,V>, m2:map<K,V>, m3:map<K,V>)
    requires forall i, j :: i in m1 && j in m2 ==> i != j
    requires m3 == m1 + m2
    ensures |m3| == |m1| + |m2|
  {
    assert forall k :: k in m3 <==> k in m1 || k in m2;
    assert forall k :: k in m1 ==> !(k in m2);
    assert forall k :: k in m2 ==> !(k in m1);
    assert |m1.Keys + m2.Keys| == |m1.Keys| + |m2.Keys|;
    // assert |m1 + m2| == |m1| + |m2|;
  }

  /**  */
  lemma lemma_RemoveAllSatisfiedCRequestsProducesHeaderSubset(
    requests:seq<CRequest>,
    headers:set<CRequestHeader>,
    requests':seq<CRequest>,
    headers':set<CRequestHeader>,
    r:CRequest
    )
    requires SeqIsValid(requests, CRequestIsValid)
    requires SeqIsValid(requests', CRequestIsValid)
    requires CRequestIsValid(r)
    requires HeadersMatch(requests, headers)
    requires HeadersMatch(requests', headers')
    requires requests' == CRemoveAllSatisfiedRequestsInSequence(requests, r)
    ensures  headers' <= headers
  {
    forall h | h in headers'
      ensures h in headers
    {
      var i := lemma_HeadersMatchImpliesEveryHeaderHasACorrespondingEntry(requests', headers', h);
      lemma_RemoveAllSatisfiedCRequestsProducesCRequestSubset(requests, r);
      assert requests'[i] in requests;
    }
  }

  lemma lemma_RemoveAllSatisfiedCRequestsProducesReqMapSubset(
    requests:seq<CRequest>,
    reqm:map<CRequestHeader, CAppMessage>,
    requests':seq<CRequest>,
    reqm':map<CRequestHeader, CAppMessage>,
    r:CRequest
    )
    requires SeqIsValid(requests, CRequestIsValid)
    requires SeqIsValid(requests', CRequestIsValid)
    requires CRequestIsValid(r)
    requires ReqMapMatch(requests, reqm)
    requires ReqMapMatch(requests', reqm')
    requires requests' == CRemoveAllSatisfiedRequestsInSequence(requests, r)
    // ensures  |reqm'| <= |reqm|
    ensures forall h :: h in reqm' ==> h in reqm 
  {
    forall h | h in reqm'
      ensures h in reqm
    {
      var i := lemma_ReqMapMatchImpliesEveryHeaderHasACorrespondingEntry(requests', reqm', h);
      lemma_RemoveAllSatisfiedCRequestsProducesCRequestSubset(requests, r);
      assert requests'[i] in requests;
    }
  }

  lemma lemma_RemoveAllSatisfiedCRequestsProducesCRequestSubset(requests:seq<CRequest>, r:CRequest)
    requires SeqIsValid(requests, CRequestIsValid)
    requires CRequestIsValid(r)
    ensures  forall r' :: r' in CRemoveAllSatisfiedRequestsInSequence(requests, r) ==> r' in requests
  {
  }

  predicate ElectionRequestQueueValid(queue:seq<CRequest>) 
  {
    forall i :: 0 <= i < |queue| ==> CRequestIsValid(queue[i])
  }

  lemma lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(s:seq<CRequest>, r:CRequest)
    requires SeqIsAbstractable(s, AbstractifyCRequestToRequest)
    requires CRequestIsAbstractable(r)
    ensures  SeqIsAbstractable(CRemoveAllSatisfiedRequestsInSequence(s, r), AbstractifyCRequestToRequest)
    ensures  AbstractifySeq(CRemoveAllSatisfiedRequestsInSequence(s, r), AbstractifyCRequestToRequest) 
            == RemoveAllSatisfiedRequestsInSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCRequestToRequest(r))
    ensures  |CRemoveAllSatisfiedRequestsInSequence(s, r)| <= |s|
    ensures ElectionRequestQueueValid(s) ==> ElectionRequestQueueValid(CRemoveAllSatisfiedRequestsInSequence(s, r))
  {
    // lemma_RemoveAllSatisfiedCRequestsInSequenceAbstractable(s, r);
    // reveal AbstractifyCRequestsSeqToRequestsSeq();

    if |s| == 0
    {
      return;
    }

    assert SeqIsAbstractable(s, AbstractifyCRequestToRequest);
    assert forall i :: i in s ==> CRequestIsAbstractable(i);
    assert forall i :: 0 <= i < |s| ==> CRequestIsAbstractable(s[i]);
    if AbstractifyCRequestToRequest(s[0]).client == AbstractifyCRequestToRequest(r).client
    {
      lemma_AbstractifyEndPointToNodeIdentity_injective(s[0].client, r.client);
    }

    lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(s[1..], r);
  }

  lemma lemma_BoundCRequestSequence(s:seq<CRequest>, lengthBound:CUpperBound)
    // requires |s| < 0x1_0000_0000_0000_0000
    requires SeqIsValid(s, CRequestIsValid)
    // requires forall i :: i in s ==> i.CRequest? && CRequestIsValid(i)
    requires SeqIsAbstractable(s, AbstractifyCRequestToRequest)
    ensures  BoundRequestSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCUpperBoundToUpperBound(lengthBound))
            == AbstractifySeq(CBoundRequestSequence(s, lengthBound), AbstractifyCRequestToRequest)
    // ensures |CBoundRequestSequence(s, lengthBound)| <= lengthBdound.n
  {
  }

  lemma lemma_AddNewReqPreservesHeaderMatches(s1:seq<CRequest>,  headers1:set<CRequestHeader>, 
                                            s2:seq<CRequest>,  headers2:set<CRequestHeader>,
                                            s1':seq<CRequest>, headers1':set<CRequestHeader>,
                                            s2':seq<CRequest>, headers2':set<CRequestHeader>,
                                            r:CRequest)
    requires SeqIsValid(s1, CRequestIsValid)
    requires SeqIsValid(s2, CRequestIsValid)
    requires SeqIsValid(s1', CRequestIsValid)
    requires SeqIsValid(s2', CRequestIsValid)
    requires CRequestIsValid(r)
    requires HeadersMatch(s1, headers1)
    requires HeadersMatch(s2, headers2)
    requires HeadersMatch(s1 + s2, headers1 + headers2)
    requires HeadersMatch(s1', headers1')
    requires HeadersMatch(s2', headers2')
    requires headers1' == headers1;
    requires s1' == s1
    // requires forall i :: i in s2 ==> i in s2'
    requires forall req :: req in s2' && !CRequestsMatch(req, r) ==> req in s2
    requires forall h :: h in headers2' && h != CRequestHeader(r.client, r.seqno) ==> h in headers2
    requires forall other_r :: other_r in s1 || other_r in s2 ==> !CRequestsMatch(other_r, r)
    ensures  HeadersMatch(s1' + s2', headers1' + headers2')
  {
    var total_s := s1' + s2'; 
    var total_h := headers1' + headers2'; 
    forall i,j | 0 <= i < j < |total_s| && CRequestsMatch(total_s[i], total_s[j]) 
      ensures i == j
    {
      if j < |s1'| {
        assert total_s[i] in s1 && total_s[j] in s1;
        assert i == j;
      } else if i >= |s1'| {
        assert total_s[i] in s2 && total_s[j] in s2;
        assert i == j;
      } else {
        assert i < |s1'| && j >= |s1'|;
        assert total_s[i] in s1;
        // lemma_newseqconstains(total_s[j], s2);
        assert total_s[j] in s2;
        var tot_s := s1 + s2;
        assert total_s[i] in tot_s && total_s[j] in tot_s;
        var i' :| 0 <= i' < |tot_s| && total_s[i] == tot_s[i'];
        var j' :| 0 <= j' < |tot_s| && total_s[j] == tot_s[j'];
        assert HeadersMatch(tot_s, headers1 + headers2);
        if (i' < j') {
          assert CRequestsMatch(tot_s[i'], tot_s[j']);
        } else if (i' > j') {
          assert CRequestsMatch(tot_s[j'], tot_s[i']);
        }
        assert i' == j';
        assert total_s[i] == total_s[j];
        if (total_s[j] in s1) {
          i' :| 0 <= i' < |s1| && total_s[j] == s1[i'];
          j' :| 0 <= j' < |s2| && total_s[j] == s2[j'];
          assert total_s[j] == tot_s[i'];
          assert total_s[j] == tot_s[|s1| + j'];
        }
        assert total_s[j] !in s1;
        assert i == j;
      }
    }

    var header_seq := [];
    var i := 0;
    while i < |total_s|
      invariant 0 <= i <= |total_s|
      invariant |header_seq| == i
      invariant forall j :: 0 <= j < i ==> header_seq[j] == ExtractHeader(total_s[j])
    {
      header_seq := header_seq + [ExtractHeader(total_s[i])];
      i := i + 1;
    }
    
      
    forall i', j' | 0 <= i' < |header_seq| && 0 <= j' < |header_seq| && header_seq[i'] == header_seq[j']
      ensures i' == j'
    {
      assert header_seq[i'] == ExtractHeader(total_s[i']);
      assert header_seq[j'] == ExtractHeader(total_s[j']);
      if i' < j' {
        assert CRequestsMatch(total_s[i'], total_s[j']);  // OBSERVE
      } else if j' < i' {
        assert CRequestsMatch(total_s[j'], total_s[i']);  // OBSERVE
      }
    }
    forall ensures SeqIsUnique(header_seq)
    {
      reveal SeqIsUnique();
    }

    //var headers := set r | r in total_s :: ExtractHeader(r);
    var header_set := UniqueSeqToSet(header_seq);
    lemma_seqs_set_cardinality(header_seq, header_set);
    forall h | h in header_set
      ensures h in total_h
    {
    }

    forall h | h in total_h
      ensures h in header_set
    {
      if h in headers1' {
        var j := FindMatchingRequest(s1', headers1', h); 
        assert total_s[j] == s1'[j];
        assert header_seq[j] == ExtractHeader(total_s[j]);
        assert header_seq[j] == h;
        assert header_seq[j] in header_seq;
        assert header_seq[j] in header_set;
      } else {
        assert h in headers2';
        var j := FindMatchingRequest(s2', headers2', h); 
        var j_offset := j + |s1'|;
        assert total_s[j_offset] == s2'[j];
        assert header_seq[j_offset] == ExtractHeader(total_s[j_offset]);
        assert header_seq[j_offset] == h;
        assert header_seq[j_offset] in header_seq;
        assert header_seq[j_offset] in header_set;
      }
    }
    lemma_MapSetCardinalityOver(total_h, header_set, h => h);
    assert |total_h| == |header_set|;       // OBSERVE
  }

  // lemma{:axiom} lemma_newseqconstains(r:CRequest,s:seq<CRequest>)
  //   ensures r in s

  function ExtractHeader(req:CRequest) : CRequestHeader
  {
    CRequestHeader(req.client, req.seqno)
  }

  
  lemma FindMatchingRequest(s:seq<CRequest>, headers:set<CRequestHeader>, header:CRequestHeader) returns (index:int)
    requires SeqIsValid(s, CRequestIsValid) 
    requires HeadersMatch(s, headers)
    requires header in headers
    requires |s| >= 1
    ensures  0 <= index < |s|
    ensures  CRequestHeader(s[index].client, s[index].seqno) == header
  {
    if |s| == 1 {
      assert CRequestHeader(s[0].client, s[0].seqno) in headers;
      assert |headers| == 1;
      ThingsIKnowAboutASingletonSet(headers, CRequestHeader(s[0].client, s[0].seqno), header);
      return 0;
    } else {
      var head := CRequestHeader(s[0].client, s[0].seqno);
      if head == header {
        return 0;
      } else {
        var new_set := headers - { head };
        forall r | r in s[1..]
          ensures CRequestHeader(r.client, r.seqno) in new_set;
        {
          if CRequestHeader(r.client, r.seqno) != head {
            assert CRequestHeader(r.client, r.seqno) in new_set;
          } else {
            var j :| 0 <= j < |s[1..]| && s[1..][j] == r;
            assert s[j+1] == s[1..][j] == r;
            assert CRequestsMatch(s[0], s[j+1]);
            assert j+1 == 0;
            assert false;
          }
        }
        index := FindMatchingRequest(s[1..], new_set, header);
        index := index + 1;
      }
    }
  }

  lemma ThingsIKnowAboutSubmap<K(!new),V(!new)>(x:map<K,V>, y:map<K,V>)
    requires forall p :: p in x ==> p in y
    requires exists p :: p in y && p !in x
    ensures |x|<|y|
  {
    if (x!=map[]) {
      var e :| e in x;
      ThingsIKnowAboutSubmap(RemoveElt(x,e), RemoveElt(y,e));
    }
    else{
      assert |x| == 0;
      assert |y| > 0;
    }
  }

  lemma ThingsIKnowAboutASingletonMap<K(!new),V(!new)>(foo:map<K,V>, x:K, y:K)
    requires |foo|==1
    requires x in foo
    requires y in foo
    ensures x==y
  {
    if (x!=y) {
      var m := map[x:=foo[x]];
      assert forall p :: p in m ==> p in foo;
      assert exists p :: p in foo ==> p !in m;
      ThingsIKnowAboutSubmap(m, foo);
      assert |m| < |foo|;
      assert |foo|>1;
      assert false;
    }
  }

  lemma FindMatchingRequestForReqMap(s:seq<CRequest>, rmap:map<CRequestHeader, CAppMessage>, header:CRequestHeader) returns (index:int)
    requires SeqIsValid(s, CRequestIsValid) 
    requires ReqMapMatch(s, rmap)
    requires header in rmap
    requires |s| >= 1
    ensures  0 <= index < |s|
    ensures  CRequestHeader(s[index].client, s[index].seqno) == header
  {
    if |s| == 1 {
      assert CRequestHeader(s[0].client, s[0].seqno) in rmap;
      assert |rmap| == 1;
      ThingsIKnowAboutASingletonMap(rmap, CRequestHeader(s[0].client, s[0].seqno), header);
      return 0;
    } else {
      var head := CRequestHeader(s[0].client, s[0].seqno);
      if head == header {
        return 0;
      } else {
        var new_map := RemoveElt(rmap, head);
        // lemma_ReqSeqIsUnique(s);
        forall r | r in s[1..]
          ensures CRequestHeader(r.client, r.seqno) in new_map
        {
          if CRequestHeader(r.client, r.seqno) != head {
            assert CRequestHeader(r.client, r.seqno) in new_map;
          } else {
            // var j :| 0 <= j < |s[1..]| && s[1..][j] == r;
            // assert s[j+1] == s[1..][j] == r;
            // assert CRequestsMatch(s[0], s[j+1]);
            // assert j+1 == 0;
            assert forall i, j :: 0 <= i < |s| && 0 <= j < |s| && CRequestsMatch(s[i], s[j]) ==> i == j;
            assert false;
          }
        }

        index := FindMatchingRequestForReqMap(s[1..], new_map, header);
        index := index + 1;
      }
    }
  }


  lemma lemma_HeadersMatchAddition(requests:seq<CRequest>, headers:set<CRequestHeader>, req:CRequest)
    requires SeqIsValid(requests, CRequestIsValid) 
    requires CRequestIsValid(req)
    requires HeadersMatch(requests, headers)
    requires !(exists earlier_req :: earlier_req in requests && CRequestsMatch(earlier_req, req))
    ensures  HeadersMatch(requests + [req], headers + { CRequestHeader(req.client, req.seqno) })
  {
    var header := CRequestHeader(req.client, req.seqno);
    if header in headers {
      ghost var i := FindMatchingRequest(requests, headers, header); 
      assert requests[i] in requests && CRequestsMatch(requests[i], req);
    }
    assert !(header in headers);
  }

  lemma lemma_ReqMapMatchAddition(requests:seq<CRequest>, req_map:map<CRequestHeader, CAppMessage>, req:CRequest)
    requires SeqIsValid(requests, CRequestIsValid) 
    requires CRequestIsValid(req)
    requires ReqMapMatch(requests, req_map)
    requires !(exists earlier_req :: earlier_req in requests && CRequestsMatch(earlier_req, req))
    ensures  ReqMapMatch(requests + [req], req_map[ CRequestHeader(req.client, req.seqno) := req.request])
  {
    var header := CRequestHeader(req.client, req.seqno);
    if header in req_map {
      ghost var i := FindMatchingRequestForReqMap(requests, req_map, header);
      assert requests[i] in requests && CRequestsMatch(requests[i], req);
    }
    assert !(header in req_map);
  }

  lemma  lemma_ReqMapMatch2(requests:seq<CRequest>, reqmap:map<CRequestHeader, CAppMessage>)
    requires SeqIsValid(requests, CRequestIsValid) 
    requires ReqMapMatch(requests, reqmap)
    ensures (forall r :: r in requests ==> CRequestHeader(r.client, r.seqno) in reqmap && r.request == reqmap[CRequestHeader(r.client, r.seqno)])
  {

  }

  lemma {:axiom} lemma_ReqMapNotIntersect(m1:map<CRequestHeader, CAppMessage>, m2:map<CRequestHeader, CAppMessage>)
    ensures forall i :: i in m1 ==> i !in m2
    ensures forall i :: i in m2 ==> i !in m1

  lemma lemma_AddNewReqPreservesReqMapMatches(s1:seq<CRequest>,  map1:map<CRequestHeader, CAppMessage>, 
                                            s2:seq<CRequest>,  map2:map<CRequestHeader, CAppMessage>,
                                            s1':seq<CRequest>, map1':map<CRequestHeader, CAppMessage>,
                                            s2':seq<CRequest>, map2':map<CRequestHeader, CAppMessage>,
                                            r:CRequest)
    requires SeqIsValid(s1, CRequestIsValid)
    requires SeqIsValid(s2, CRequestIsValid)
    requires SeqIsValid(s1', CRequestIsValid)
    requires SeqIsValid(s2', CRequestIsValid)
    requires CRequestIsValid(r)
    requires ReqMapMatch(s1, map1)
    requires ReqMapMatch(s2, map2)
    requires ReqMapMatch(s1 + s2, map1 + map2)
    requires ReqMapMatch(s1', map1')
    requires ReqMapMatch(s2', map2')
    requires map1' == map1;
    requires s1' == s1
    // requires forall i :: i in s2 ==> i in s2'
    requires forall req :: req in s2' && !CRequestsMatch(req, r) ==> req in s2
    requires forall h :: h in map2' && h != CRequestHeader(r.client, r.seqno) ==> h in map2
    requires forall other_r :: other_r in s1 || other_r in s2 ==> !CRequestsMatch(other_r, r)
    ensures  ReqMapMatch(s1' + s2', map1' + map2')
  {
    // lemma_ReqMapMatch(s1' + s2', map1' + map2');
    var total_s := s1' + s2'; 
    var total_h := map1' + map2'; 
    forall i,j | 0 <= i < j < |total_s| && CRequestsMatch(total_s[i], total_s[j]) 
      ensures i == j
    {
      if j < |s1'| {
        assert total_s[i] in s1 && total_s[j] in s1;
        assert i == j;
      } else if i >= |s1'| {
        assert total_s[i] in s2 && total_s[j] in s2;
        assert i == j;
      } else {
        assert i < |s1'| && j >= |s1'|;
        assert total_s[i] in s1;
        // lemma_newseqconstains(total_s[j], s2);
        assert total_s[j] in s2;
        var tot_s := s1 + s2;
        assert total_s[i] in tot_s && total_s[j] in tot_s;
        var i' :| 0 <= i' < |tot_s| && total_s[i] == tot_s[i'];
        var j' :| 0 <= j' < |tot_s| && total_s[j] == tot_s[j'];
        assert ReqMapMatch(tot_s, map1 + map2);
        lemma_ReqMapMatch2(tot_s, map1+map2);
        if (i' < j') {
          assert CRequestsMatch(tot_s[i'], tot_s[j']);
        } else if (i' > j') {
          assert CRequestsMatch(tot_s[j'], tot_s[i']);
        }
        assert i' == j';
        assert total_s[i] == total_s[j];
        if (total_s[j] in s1) {
          i' :| 0 <= i' < |s1| && total_s[j] == s1[i'];
          j' :| 0 <= j' < |s2| && total_s[j] == s2[j'];
          assert total_s[j] == tot_s[i'];
          assert total_s[j] == tot_s[|s1| + j'];
        }
        assert total_s[j] !in s1;
        assert i == j;
      }
    }

    lemma_ReqMapMatch2(s1, map1);
    lemma_ReqMapMatch2(s2, map2);
    lemma_ReqMapMatch2(s1+s2, map1+map2);
    lemma_ReqMapMatch2(s1', map1');
    lemma_ReqMapMatch2(s2', map2');
    

    // forall h | h in total_h
    //   ensures exists i :: i in total_s && CRequestHeader(i.client, i.seqno) == h && total_h[h] == i.request
    // {
    //   if h in map1'{
    //     var j := FindMatchingRequestForReqMap(s1', map1', h); 
    //     assert total_s[j] == s1'[j];
    //     assert h == ExtractHeader(total_s[j]);
        
    //   }
    // }

    var header_seq := [];
    var i := 0;
    while i < |total_s|
      invariant 0 <= i <= |total_s|
      invariant |header_seq| == i
      invariant forall j :: 0 <= j < i ==> header_seq[j] == ExtractHeader(total_s[j])
    {
      header_seq := header_seq + [ExtractHeader(total_s[i])];
      i := i + 1;
    }
    
      
    forall i', j' | 0 <= i' < |header_seq| && 0 <= j' < |header_seq| && header_seq[i'] == header_seq[j']
      ensures i' == j'
    {
      assert header_seq[i'] == ExtractHeader(total_s[i']);
      assert header_seq[j'] == ExtractHeader(total_s[j']);
      if i' < j' {
        assert CRequestsMatch(total_s[i'], total_s[j']);  // OBSERVE
      } else if j' < i' {
        assert CRequestsMatch(total_s[j'], total_s[i']);  // OBSERVE
      }
    }
    forall ensures SeqIsUnique(header_seq)
    {
      reveal SeqIsUnique();
    }

    //var headers := set r | r in total_s :: ExtractHeader(r);
    assert forall j :: 0 <= j < |total_s| ==> header_seq[j] == ExtractHeader(total_s[j]);
    var header_set := UniqueSeqToSet(header_seq);
    lemma_seqs_set_cardinality(header_seq, header_set);

    var header_map := ConvertSeqToMap(header_seq, total_s);

    lemma_ReqMapNotIntersect(map1', map2');
    assert forall h :: h in header_map ==> h in header_seq;
    assert forall h :: h in map1' ==> h !in map2';
    assert forall h :: h in map2' ==> h !in map1';
    forall h | h in header_map
      ensures h in total_h
    {
      if h in map1' {
        var j := FindMatchingRequestForReqMap(s1', map1', h); 
        assert total_s[j] == s1'[j];
        assert header_seq[j] == ExtractHeader(total_s[j]);
        assert header_seq[j] == h;
        assert header_seq[j] in header_seq;
        assert header_seq[j] in header_map;
        assert header_map[h] == total_s[j].request;
        assert map1'[h] == s1'[j].request;
        assert total_h[h] == map1'[h];
        assert total_h[h] == total_s[j].request;
      } else {
        assert h in map2';
        var j := FindMatchingRequestForReqMap(s2', map2', h); 
        var j_offset := j + |s1'|;
        assert total_s[j_offset] == s2'[j];
        assert header_seq[j_offset] == ExtractHeader(total_s[j_offset]);
        assert header_seq[j_offset] == h;
        assert header_seq[j_offset] in header_seq;
        assert header_seq[j_offset] in header_map;
      }
    }

    forall h | h in total_h
      ensures h in header_map && total_h[h] == header_map[h]
    {
      if h in map1' {
        var j := FindMatchingRequestForReqMap(s1', map1', h); 
        assert total_s[j] == s1'[j];
        assert header_seq[j] == ExtractHeader(total_s[j]);
        assert header_seq[j] == h;
        assert header_seq[j] in header_seq;
        assert header_seq[j] in header_map;
        assert header_map[h] == total_s[j].request;
        assert total_h[h] == total_s[j].request;
      } else {
        assert h in map2';
        var j := FindMatchingRequestForReqMap(s2', map2', h); 
        var j_offset := j + |s1'|;
        assert total_s[j_offset] == s2'[j];
        assert header_seq[j_offset] == ExtractHeader(total_s[j_offset]);
        assert header_seq[j_offset] == h;
        assert header_seq[j_offset] in header_seq;
        assert header_seq[j_offset] in header_map;
      }
    }
    assert forall r :: r in total_s ==> CRequestHeader(r.client, r.seqno) in total_h;
    assert forall r :: r in total_s ==> CRequestHeader(r.client, r.seqno) in total_h
            && r.request == total_h[CRequestHeader(r.client, r.seqno)];
    Lemma_map2equiv(total_h, header_map);
    assert |total_h| == |header_seq|;       // OBSERVE
  }

  lemma ConvertSeqToMap(header_seq:seq<CRequestHeader>, s:seq<CRequest>) returns (m:map<CRequestHeader, CAppMessage>)
    requires SeqIsUnique(header_seq)
    requires |header_seq| == |s|
    requires forall j :: 0 <= j < |s| ==> header_seq[j] == ExtractHeader(s[j])
    ensures
            |m| == |header_seq|
            && (forall i :: 0 <= i < |s| ==> header_seq[i] in m && m[header_seq[i]] == s[i].request)
            && (forall h :: h in m ==> h in header_seq)
  {
    if |header_seq| == 0 {
      m:= map[];
      assert |m| == |header_seq|
            && (forall i :: 0 <= i < |s| ==> header_seq[i] in m && m[header_seq[i]] == s[i].request)
            && (forall h :: h in m ==> h in header_seq);
    }
    else 
    {
      var reqmap := map[];
      var i := 0;
      reveal_SeqIsUnique();
      assert SeqIsUnique(header_seq);
      assert forall i, j :: 0 <= j < i < |header_seq| ==> header_seq[i] != header_seq[j];
      while i < |s|
        invariant 0 <= i <= |s|
        invariant |reqmap| == i
        invariant (forall j :: 0 <= j < i ==> header_seq[j] in reqmap && reqmap[header_seq[j]] == s[j].request)
        invariant (forall h :: h in reqmap ==> h in header_seq[..i])
      {
        var header := header_seq[i];
        var oldmap := reqmap;
        assert |oldmap| == i;
        assert forall j :: 0 <= j < i ==> header_seq[j] in reqmap && reqmap[header_seq[j]] == s[j].request;
        assert forall j :: 0 <= j < i ==> header_seq[j] != header;
        assert forall h :: h in oldmap  ==> header != h;
        reqmap := reqmap[header := s[i].request];
        assert |reqmap| == |oldmap| + 1;
        assert reqmap == oldmap[header := s[i].request];
        i := i + 1;
      }
      m := reqmap;
    }
  }

  
  lemma lemma_CRequestsMatch()
    ensures forall r1:CRequest, r2:CRequest :: CRequestIsAbstractable(r1) && CRequestIsAbstractable(r2) ==>
              CRequestsMatch(r1, r2) == RequestsMatch(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2))
  {
    forall r1:CRequest, r2:CRequest | CRequestIsAbstractable(r1) && CRequestIsAbstractable(r2)
      ensures CRequestsMatch(r1, r2) == RequestsMatch(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2))
    {
      lemma_AbstractifyCRequestToRequest_isInjective();
      lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    }
  }

  lemma lemma_AbstractifyCRequestToRequest_isInjective()
    ensures forall v1, v2 :: CRequestIsAbstractable(v1) && CRequestIsAbstractable(v2) && AbstractifyCRequestToRequest(v1) == AbstractifyCRequestToRequest(v2) ==> v1 == v2
  {
  }

  /************************** Manually Optimization for I1 End ********************/

}

