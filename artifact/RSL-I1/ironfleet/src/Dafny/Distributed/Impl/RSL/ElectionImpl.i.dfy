include "../../Protocol/RSL/Election.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "CConfiguration.i.dfy"
include "CConstants.i.dfy"
include "../Common/Util.i.dfy"
include "../Common/UpperBound.i.dfy"

module LiveRSL__ElectionModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveRSL__CMessage_i
  import opened LiveRSL__CMessageRefinements_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__ConstantsState_i
  import opened LiveRSL__CPaxosConfiguration_i
  import opened LiveRSL__CTypes_i
  import opened LiveRSL__Election_i
  import opened LiveRSL__Types_i
  import opened Common__NodeIdentity_i
  import opened Common__SeqIsUnique_i
  import opened Common__SeqIsUniqueDef_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened Collections__Seqs_s
  import opened Collections__Sets_i
  import opened GenericRefinement_i

  /************************** AutoMan Translation ************************/
  /** 0 + 2 */
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
    ghost prev_req_set:set<CRequestHeader>
	)

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

  /** 0 + 3 */
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
	}

	function AbstractifyCElectionStateToElectionState(s: CElectionState) : ElectionState 
		requires CElectionStateIsAbstractable(s)
	{
		ElectionState(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.current_view), s.current_view_suspectors, s.epoch_end_time, s.epoch_length, AbstractifySeq(s.requests_received_this_epoch, AbstractifyCRequestToRequest), AbstractifySeq(s.requests_received_prev_epochs, AbstractifyCRequestToRequest))
	}

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

  function method CRemoveAllSatisfiedRequestsInSequence(s: seq<CRequest>, r: CRequest) : seq<CRequest> 
		requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CRequestIsValid(r)
    // ensures  forall r' :: r' in CRemoveAllSatisfiedRequestsInSequence(s, r) ==> r' in s
    ensures (forall i :: i in CRemoveAllSatisfiedRequestsInSequence(s, r) ==> i.CRequest? && CRequestIsValid(i) && i in s)
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
    var t8 := {};
    var t9 := {};
		CElectionState(t1, t2, t3, t4, t5, t6, t7, t8, t9)
	}

  /** 13 + 6 */
  /** Modified 19 lines for I1 */
  method CElectionStateProcessHeartbeat(es: CElectionState, p: CPacket, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (es':CElectionState) 
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

    ensures CElectionStateIsValid(es') && ElectionStateProcessHeartbeat(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCPacketToRslPacket(p), clock)
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
            prev_req_set.AddSet(cur_req_set);
            cur_req_set.RemoveAll();
            new_set := BoundCRequestHeaders(new_seq, new_set, es.constants.all.params.max_integer_val, prev_req_set); /** End */

            
            // var t1 := 
            var new_epoch_length := UpperBoundedAdditionImpl(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); 
            es' := es.(current_view := p.msg.bal_heartbeat, current_view_suspectors := if p.msg.suspicious then {sender_index} else {}, epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := [],
                      /** Manually Added for I1 */
                      cur_req_set := {},
                      prev_req_set := new_set); /** End */
          } else { 
            es' := es; 
          }
        }
    }
	}

  /** 15 + 6 */
  /** 21 lines for I1 */
	method CElectionStateCheckForViewTimeout(es: CElectionState, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (es':CElectionState) 
		requires CElectionStateIsValid(es)
		// ensures var es' := CElectionStateCheckForViewTimeout(es, clock); 
    /** Manually Added for I1 */
    requires MutableSet.SetOf(cur_req_set) == es.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == es.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures MutableSet.SetOf(cur_req_set) == es'.cur_req_set
    ensures MutableSet.SetOf(prev_req_set) == es'.prev_req_set /** End */

    ensures CElectionStateIsValid(es') && ElectionStateCheckForViewTimeout(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), clock)
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
                  prev_req_set := es.cur_req_set);  /** Manually Added for I1 */
        // t1; 
        // t1 
      } else {
        // var t1 := 
        /** Manually Added for I1 */
        ghost var new_set := es.prev_req_set + es.cur_req_set;
        prev_req_set.AddSet(cur_req_set);
        cur_req_set.RemoveAll();
        var new_seq := es.requests_received_prev_epochs + es.requests_received_this_epoch;
        new_set := BoundCRequestHeaders(new_seq, new_set, es.constants.all.params.max_integer_val, prev_req_set); /** End */

        es' := es.(current_view_suspectors := es.current_view_suspectors + {es.constants.my_index}, epoch_end_time := UpperBoundedAdditionImpl(clock, es.epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := [],
                  cur_req_set := {}, /** Manually Added for I1 */
                  prev_req_set := new_set);  /** Manually Added for I1 */
        // t1; 
        // t1; 		
		// t1
      }
    }
	}

  /** 10 + 6 */
  /** 16 lines for I1 */
  method CElectionStateCheckForQuorumOfViewSuspicions(es: CElectionState, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (es':CElectionState) 
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
      prev_req_set.AddSet(cur_req_set);
      cur_req_set.RemoveAll();
      new_set := BoundCRequestHeaders(new_seq, new_set, es.constants.all.params.max_integer_val, prev_req_set);

      es' := es.(current_view := CComputeSuccessorView(es.current_view, es.constants.all), current_view_suspectors := {}, epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := [],
                cur_req_set := {}, /** Manually Added for I1 */
                prev_req_set := new_set); /** Manually Added for I1 */
    //   t1; 
    // t1; 		
		// t1
    }
	}

  
	// function method CElectionStateReflectReceivedRequest(es: CElectionState, req: CRequest) : CElectionState 
	// 	requires CElectionStateIsValid(es)
	// 	requires CRequestIsValid(req)
	// 	ensures var es' := CElectionStateReflectReceivedRequest(es, req); CElectionStateIsValid(es') && ElectionStateReflectReceivedRequest(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestToRequest(req))
	// {
	// 	var t1 := if (exists earlier_req :: earlier_req in es.requests_received_prev_epochs && CRequestsMatch(earlier_req, req)) then var t1 := es; t1 else var t1 := if (exists earlier_req :: earlier_req in es.requests_received_this_epoch && CRequestsMatch(earlier_req, req)) then var t1 := es; t1 else var t1 := es.(requests_received_this_epoch := CBoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val)); t1; t1; 		
	// 	t1
	// }

  function method CElectionStateReflectReceivedRequest(es: CElectionState, req: CRequest) : CElectionState 
		requires CElectionStateIsValid(es)
		requires CRequestIsValid(req)
		ensures var es' := CElectionStateReflectReceivedRequest(es, req); CElectionStateIsValid(es') && ElectionStateReflectReceivedRequest(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestToRequest(req))
	{
		var t1 := 
    if (exists earlier_req :: earlier_req in es.requests_received_prev_epochs && CRequestsMatch(earlier_req, req)) then 
      var t1 := es; 
      t1 
    else 
      var t1 := 
      if (exists earlier_req :: earlier_req in es.requests_received_this_epoch && CRequestsMatch(earlier_req, req)) then 
        var t1 := es; 
        t1 
      else 
        var t1 := es.(requests_received_this_epoch := CBoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val)); 
        t1; 
      t1; 		
      lemma_CElectionStateValid(t1);
		t1
	}

  function method CRemoveExecutedRequestBatch(reqs: seq<CRequest>, batch: CRequestBatch) : seq<CRequest> 
		requires (forall i :: i in reqs ==> CRequestIsValid(i))
		requires CRequestBatchIsValid(batch)
		decreases |batch|

    ensures (forall i :: i in CRemoveExecutedRequestBatch(reqs, batch) ==> i.CRequest? && CRequestIsValid(i))
    ensures AbstractifySeq(CRemoveExecutedRequestBatch(reqs, batch), AbstractifyCRequestToRequest) == RemoveExecutedRequestBatch(AbstractifySeq(reqs, AbstractifyCRequestToRequest), AbstractifyCRequestBatchToRequestBatch(batch))
		// ensures CRemoveExecutedRequestBatch(reqs, batch) == RemoveExecutedRequestBatch(AbstractifySeq(reqs, AbstractifyCRequestToRequest), AbstractifyCRequestBatchToRequestBatch(batch))
	{
		if |batch| == 0 then 
			reqs 
		else 
			CRemoveExecutedRequestBatch(CRemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), batch[1..])
	}

	function method CElectionStateReflectExecutedRequestBatch(es: CElectionState, batch: CRequestBatch) : CElectionState 
		requires CElectionStateIsValid(es)
		requires CRequestBatchIsValid(batch)
		ensures var es' := CElectionStateReflectExecutedRequestBatch(es, batch); CElectionStateIsValid(es') && ElectionStateReflectExecutedRequestBatch(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestBatchToRequestBatch(batch))
	{
		var t1 := 
    es.(
      requests_received_prev_epochs := CRemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch), 
      requests_received_this_epoch := CRemoveExecutedRequestBatch(es.requests_received_this_epoch, batch)
    ); 		
    lemma_CElectionStateValid(t1);
		t1
	}

  lemma {:axiom} lemma_CElectionStateValid(ces:CElectionState)
    requires (forall i :: i in ces.requests_received_this_epoch ==> CRequestIsValid(i)) 
    requires (forall i :: i in ces.requests_received_prev_epochs ==> CRequestIsValid(i)) 
    ensures HeadersMatch(ces.requests_received_this_epoch, ces.cur_req_set)
    ensures HeadersMatch(ces.requests_received_prev_epochs, ces.prev_req_set)
    ensures HeadersMatch(ces.requests_received_prev_epochs + ces.requests_received_this_epoch, ces.prev_req_set + ces.cur_req_set)

  /************************** AutoMan Translation End ************************/

  
  /************************** Manually Optimization for I1 ********************/
  /** 1 + 0 */
  datatype CRequestHeader = CRequestHeader(client:EndPoint, seqno:int)

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



  method{:timeLimitMultiplier 2} CRemoveAllSatisfiedRequestsInSequence_I1(
    requests:seq<CRequest>,
    ghost headers:set<CRequestHeader>,
    cur_req_set:MutableSet<CRequestHeader>,
    r:CRequest
    ) returns (
    requests':seq<CRequest>,
    ghost headers':set<CRequestHeader>
    )
    requires SeqIsValid(requests,CRequestIsValid)
    requires CRequestIsValid(r)
    requires HeadersMatch(requests, headers)
    requires MutableSet.SetOf(cur_req_set) == headers
    modifies cur_req_set
    ensures  requests' == CRemoveAllSatisfiedRequestsInSequence(requests, r) /** Refines I0 */
    ensures  HeadersMatch(requests', headers')
    ensures  MutableSet.SetOf(cur_req_set) == headers'
  {
    var i := 0;
    var len := |requests|;
    ghost var removed_headers:set<CRequestHeader> := {};
    headers' := {};
    requests' := [];
    i := 0;

    lemma_EmptyHeadersMatch(requests', headers');

    while i < len
      invariant 0 <= i <= len
      invariant SeqIsValid(requests',CRequestIsValid)
      invariant HeadersMatch(requests', headers')
      invariant forall r' :: r' in requests' ==> r' in requests[..i]
      invariant requests' == CRemoveAllSatisfiedRequestsInSequence(requests[..i], r)
      invariant MutableSet.SetOf(cur_req_set) == headers - removed_headers
      invariant headers' + removed_headers == HeadersFromPrefix(requests, i as int)
      invariant removed_headers * headers' == {}
    {
      ghost var old_requests' := requests';
      ghost var old_headers' := headers';

      lemma_RemoveAllSatisfiedCRequestsInSequenceUpdate(requests, r, i as int);

      var h := CRequestHeader(requests[i].client, requests[i].seqno);
      if h in removed_headers || h in headers'
      {
        var j :| 0 <= j < i && h == CRequestHeader(requests[j].client, requests[j].seqno);
        assert CRequestsMatch(requests[j], requests[i]);
        assert false;
      }
          
      if CRequestSatisfiedBy(requests[i], r) {
        cur_req_set.Remove(h);
        removed_headers := removed_headers + {h};
      }
      else {
        headers' := headers' + {h};
        requests' := requests' + [requests[i]];
        lemma_AddingOneHeaderPreservesMatch(old_requests', old_headers', requests[i], requests', headers');
      }

      lemma_HeadersFromPrefixIncrease(requests, i as int);
      i := i + 1;
    }
    assert requests[..i] == requests;
    lemma_HeadersMatchImpliesHeadersFromPrefix(requests, headers);
  }


  method {:timeLimitMultiplier 1} CElectionStateReflectExecutedRequestBatch_I1(ces:CElectionState, creqb:CRequestBatch, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) 
    returns (ces':CElectionState)
    requires CElectionStateIsValid(ces)
    requires CRequestBatchIsValid(creqb)
    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == ces.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == ces.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  CElectionStateIsValid(ces')
    ensures  ElectionStateReflectExecutedRequestBatch(AbstractifyCElectionStateToElectionState(ces), AbstractifyCElectionStateToElectionState(ces'), AbstractifyCRequestBatchToRequestBatch(creqb))
    ensures  CElectionStateEqual(ces', CElectionStateReflectExecutedRequestBatch(ces, creqb)) /** Refines I0 */
    ensures MutableSet.SetOf(cur_req_set) == ces'.cur_req_set
    ensures MutableSet.SetOf(prev_req_set) == ces'.prev_req_set
    decreases |creqb|
  {
    ghost var es  := AbstractifyCElectionStateToElectionState(ces);
    var i:uint64 := 0;
    assert AbstractifyCRequestBatchToRequestBatch(creqb[..i]) == [];
    var tempces' := ces;
    ghost var ces_0 := ces;

    while i < |creqb| as uint64
      invariant 0 <= i as int <= |creqb|
      invariant CElectionStateIsAbstractable(tempces')
      invariant CElectionStateIsValid(tempces')
      invariant ElectionStateReflectExecutedRequestBatch(es, AbstractifyCElectionStateToElectionState(tempces'), AbstractifyCRequestBatchToRequestBatch(creqb[..i]))
      invariant CElectionStateEqual(tempces', CElectionStateReflectExecutedRequestBatch(ces_0, creqb[..i]))
      invariant MutableSet.SetOf(cur_req_set) == tempces'.cur_req_set
      invariant MutableSet.SetOf(prev_req_set) == tempces'.prev_req_set
    { 
      var creq := creqb[i];

      ghost var req := AbstractifyCRequestToRequest(creq);
      ghost var es':ElectionState := AbstractifyCElectionStateToElectionState(tempces');

      ghost var ces'_0 := tempces';
        
      lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(tempces'.requests_received_prev_epochs, creq);
      lemma_RemoveAllSatisfiedCRequestsInSequenceProperties(tempces'.requests_received_this_epoch, creq);

      assert ElectionStateReflectExecutedRequestBatch(es, AbstractifyCElectionStateToElectionState(tempces'), AbstractifyCRequestBatchToRequestBatch(creqb[..i]));
      
      ghost var es'' := es'.(requests_received_prev_epochs := RemoveAllSatisfiedRequestsInSequence(es'.requests_received_prev_epochs, req),
                            requests_received_this_epoch := RemoveAllSatisfiedRequestsInSequence(es'.requests_received_this_epoch, req));
      
      
      
      // ghost var old_tempces'_0 := tempces';

      var prevEpoch;
      ghost var prevEpochSet;
      prevEpoch, prevEpochSet := CRemoveAllSatisfiedRequestsInSequence_I1(tempces'.requests_received_prev_epochs, tempces'.prev_req_set, prev_req_set, creq);
      var thisEpoch; 
      ghost var thisEpochSet;
      thisEpoch, thisEpochSet := CRemoveAllSatisfiedRequestsInSequence_I1(tempces'.requests_received_this_epoch, tempces'.cur_req_set, cur_req_set, creq);

      ghost var prevEpoch_0 := CRemoveAllSatisfiedRequestsInSequence(tempces'.requests_received_prev_epochs, creq);
      ghost var thisEpoch_0 := CRemoveAllSatisfiedRequestsInSequence(tempces'.requests_received_this_epoch, creq);
      // // assert prevEpoch_0
      assert prevEpoch == prevEpoch_0;
      assert thisEpoch == thisEpoch_0;
      ghost var ces''_0 := ces'_0.(requests_received_prev_epochs := prevEpoch_0,
                                        requests_received_this_epoch := thisEpoch_0);

      lemma_RemoveAllSatisfiedPreservesHeaderMatches(tempces'.requests_received_prev_epochs, tempces'.prev_req_set,
                                                    tempces'.requests_received_this_epoch, tempces'.cur_req_set,
                                                    prevEpoch, prevEpochSet,
                                                    thisEpoch, thisEpochSet,
                                                    creq);

      tempces' := tempces'.(requests_received_prev_epochs := prevEpoch,
                            requests_received_this_epoch := thisEpoch,
                            cur_req_set := thisEpochSet,
                            prev_req_set := prevEpochSet);

      // assert CElectionStateEqual(tempces', tempces'_0);

      assert {:split_here} true;
      assert AbstractifyCRequestBatchToRequestBatch(creqb[..i]) == AbstractifyCRequestBatchToRequestBatch(creqb)[..i];
      assert AbstractifyCRequestBatchToRequestBatch(creqb[..i+1]) == AbstractifyCRequestBatchToRequestBatch(creqb)[..i+1];
      lemma_SequenceRemoveAllSatisfied(es.requests_received_prev_epochs, AbstractifyCRequestBatchToRequestBatch(creqb), i as int, es'.requests_received_prev_epochs, es''.requests_received_prev_epochs);
      lemma_SequenceRemoveAllSatisfied(es.requests_received_this_epoch, AbstractifyCRequestBatchToRequestBatch(creqb), i as int, es'.requests_received_this_epoch, es''.requests_received_this_epoch);
      assert CElectionStateIsValid(ces_0);
      assert (forall i :: i in ces_0.requests_received_this_epoch ==> CRequestIsValid(i));
      assert CRequestBatchIsValid(creqb);
      assert ces'_0.requests_received_prev_epochs == CRemoveExecutedRequestBatch(ces_0.requests_received_prev_epochs, creqb[.. i]);
      lemma_SequenceRemoveAllSatisfied2(ces_0.requests_received_prev_epochs, creqb, i as int, ces'_0.requests_received_prev_epochs, ces''_0.requests_received_prev_epochs);
      lemma_SequenceRemoveAllSatisfied2(ces_0.requests_received_this_epoch, creqb, i as int, ces'_0.requests_received_this_epoch, ces''_0.requests_received_this_epoch);
      // lemma_hb(ces_0);
      // lemma_hh(tempces', ces_0, creqb, (i+1) as int);
      assert CElectionStateEqual(tempces', CElectionStateReflectExecutedRequestBatch(ces_0, creqb[..i+1]));
      i := i + 1;
    }
    assert creqb[..i] == creqb;
    ces' := tempces';
  }


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
  ensures ElectionStateReflectReceivedRequest(AbstractifyCElectionStateToElectionState(ces), 
        AbstractifyCElectionStateToElectionState(CElectionStateReflectReceivedRequest(ces, creq)), 
        AbstractifyCRequestToRequest(creq)) 
  ensures CElectionStateEqual(ces', CElectionStateReflectReceivedRequest(ces, creq)) /** Refines I0 */
  ensures MutableSet.SetOf(cur_req_set) == ces'.cur_req_set
  ensures MutableSet.SetOf(prev_req_set) == ces'.prev_req_set
  {
    // reveal CElectionStateReflectReceivedRequest();
    ghost var req := AbstractifyCRequestToRequest(creq);
    ghost var es  := AbstractifyCElectionStateToElectionState(ces);
    ghost var es':ElectionState;

    ghost var ces_0 := ces; 

    var find_earlier := FindEarlierRequests(ces, creq, cur_req_set, prev_req_set);

    if find_earlier {
      assert exists earlier_req :: (earlier_req in ces.requests_received_prev_epochs 
                                          || earlier_req in ces.requests_received_this_epoch)
                                      && CRequestsMatch(earlier_req, creq);
      assert exists earlier_req :: (earlier_req in ces.requests_received_prev_epochs && CRequestsMatch(earlier_req, creq))
                                          || (earlier_req in ces.requests_received_this_epoch
                                      && CRequestsMatch(earlier_req, creq));
      ghost var ces'_0 := ces_0;
      ghost var ces''_0 := CElectionStateReflectReceivedRequest(ces, creq);
      assert CElectionStateEqual(ces'_0, ces''_0);
      
      ces' := ces;
      assert CElectionStateEqual(ces', CElectionStateReflectReceivedRequest(ces, creq));
    } else {
      es' := es.(requests_received_this_epoch := BoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val));
      var new_seq := ces.requests_received_this_epoch + [creq];
      var header := CRequestHeader(creq.client, creq.seqno);
      ghost var new_set := ces.cur_req_set + { header };
      cur_req_set.Add(header);
      lemma_HeadersMatchAddition(ces.requests_received_this_epoch, ces.cur_req_set, creq);
      assert HeadersMatch(new_seq, new_set);
      var bounded_seq := CBoundRequestSequence(new_seq, ces.constants.all.params.max_integer_val);
      assert MutableSet.SetOf(cur_req_set) == new_set;
      new_set := BoundCRequestHeaders(new_seq, new_set, ces.constants.all.params.max_integer_val, cur_req_set);
      ces' := ces.(requests_received_this_epoch := bounded_seq,
      cur_req_set := new_set
      );

      ghost var ces'_0 := ces_0.(
              requests_received_this_epoch := CBoundRequestSequence(
                ces_0.requests_received_this_epoch + [creq], 
                ces_0.constants.all.params.max_integer_val)
              );
      ghost var ces''_0 := CElectionStateReflectReceivedRequest(ces, creq);
      assert CElectionStateEqual(ces'_0, ces');      
      assert CElectionStateEqual(ces'_0, ces''_0);
      assert CElectionStateEqual(ces', CElectionStateReflectReceivedRequest(ces, creq));

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

  predicate CElectionStateEqual(ces1:CElectionState, ces2:CElectionState)
  {
    && ces1.constants == ces2.constants
    && ces1.current_view == ces2.current_view
    && ces1.current_view_suspectors == ces2.current_view_suspectors
    && ces1.epoch_end_time == ces2.epoch_end_time
    && ces1.epoch_length == ces2.epoch_length
    && ces1.requests_received_this_epoch == ces2.requests_received_this_epoch
    && ces1.requests_received_prev_epochs == ces2.requests_received_prev_epochs
  }

  

   /** 0 + 7 */
  predicate HeadersMatch(requests:seq<CRequest>, headers:set<CRequestHeader>)
    requires SeqIsValid(requests, CRequestIsValid) 
  {
    &&  |requests| == |headers|
    && (forall r :: r in requests ==> CRequestHeader(r.client, r.seqno) in headers)
    && (forall i,j {:trigger CRequestsMatch(requests[i], requests[j])} :: 0 <= i < j < |requests| && CRequestsMatch(requests[i], requests[j]) ==> i == j)
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

   lemma lemma_SequenceRemoveAllSatisfied2(rseq:seq<CRequest>, batch:CRequestBatch, i:int, rseq':seq<CRequest>, rseq'':seq<CRequest>)
    requires 0 <= i < |batch|
    requires (forall i :: i in rseq ==> CRequestIsValid(i))
		requires CRequestBatchIsValid(batch)
    requires rseq' == CRemoveExecutedRequestBatch(rseq, batch[..i])
    requires rseq'' == CRemoveAllSatisfiedRequestsInSequence(rseq', batch[i])
    ensures rseq'' == CRemoveExecutedRequestBatch(rseq, batch[..i+1])
    decreases i
  {
    if i > 0 {
      assert batch[1..][..i-1] == batch[1..i]; 
      assert batch[1..][..i] == batch[1..i+1]; 
      var rseqalt := CRemoveAllSatisfiedRequestsInSequence(rseq, batch[0]);
      var rseqalt' := CRemoveExecutedRequestBatch(rseqalt, batch[1..i]);
      var rseqalt'' := CRemoveAllSatisfiedRequestsInSequence(rseqalt', batch[i]);

      lemma_SequenceRemoveAllSatisfied2(rseqalt, batch[1..], i-1, rseqalt', rseqalt''); 
    }
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

