include "AppInterface.i.dfy"
include "CConstants.i.dfy"
include "AcceptorImpl.i.dfy"
include "../../Protocol/ByzRSL/Learner.i.dfy"

module LiveByzRSL__LearnerModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__CMessage_i
  // import opened LiveByzRSL__CMessageRefinements_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__Environment_i
  import opened LiveByzRSL__AcceptorModel_i
  import opened LiveByzRSL__CConfiguration_i
  import opened LiveByzRSL__Learner_i
  import opened LiveByzRSL__Message_i
  import opened LiveByzRSL__PacketParsing_i
  import opened LiveByzRSL__ConstantsState_i
  import opened LiveByzRSL__Types_i
  import opened Collections__Maps_i
  import opened Collections__Sets_i
  import opened Common__NodeIdentity_i
  import opened Common__SeqIsUnique_i
  import opened Common__SeqIsUniqueDef_i
  import opened Common__UdpClient_i
  import opened Concrete_NodeIdentity_i
  import opened GenericRefinement_i

  /************************** AutoMan Translation ************************/

  datatype CLearnerTuple = 
	CLearnerTuple(
		received_2bs: seq<CPacket>
	)

	predicate CLearnerTupleIsValid(s: CLearnerTuple) 
	{
		CLearnerTupleIsAbstractable(s) 
		&& 
		SeqIsValid(s.received_2bs, CPacketIsValid)
	}

	predicate CLearnerTupleIsAbstractable(s: CLearnerTuple) 
	{
		SeqIsAbstractable(s.received_2bs, AbstractifyCPacketToRslPacket)
	}

	function AbstractifyCLearnerTupleToLearnerTuple(s: CLearnerTuple) : LearnerTuple 
		requires CLearnerTupleIsAbstractable(s)
	{
		LearnerTuple(AbstractifySeq(s.received_2bs, AbstractifyCPacketToRslPacket))
	}
	type CLearnerState = map<COperationNumber, CLearnerTuple>

	predicate CLearnerStateIsAbstractable(s: CLearnerState) 
	{
		(forall i :: i in s ==> COperationNumberIsAbstractable(i) && CLearnerTupleIsAbstractable(s[i]))
	}

	predicate CLearnerStateIsValid(s: CLearnerState) 
	{
		CLearnerStateIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CLearnerTupleIsValid(s[i]))
	}

	function AbstractifyCLearnerStateToLearnerState(s: CLearnerState) : LearnerState 
		requires CLearnerStateIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, AbstractifyOperationNumberToCOperationNumber)
	}

  /** 6 + 0 */
  datatype CLearner = 
	CLearner(
		constants: CReplicaConstants, 
		max_ballot_seen: CBallot, 
		unexecuted_learner_state: CLearnerState
	)

  /** 0 + 10 */
	predicate CLearnerIsValid(s: CLearner) 
	{
		CLearnerIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CBallotIsValid(s.max_ballot_seen) 
		&& 
		CLearnerStateIsValid(s.unexecuted_learner_state)
	}

  /** 0 + 8 */
	predicate CLearnerIsAbstractable(s: CLearner) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CBallotIsAbstractable(s.max_ballot_seen) 
		&& 
    CLearnerStateIsAbstractable(s.unexecuted_learner_state)
	}

  /** 0 + 5 */
	function AbstractifyCLearnerToLLearner(s: CLearner) : LLearner 
		requires CLearnerIsAbstractable(s)
	{
		LLearner(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_ballot_seen), AbstractifyCLearnerStateToLearnerState(s.unexecuted_learner_state))
	}

  function method CCountMatchedValInReceived2bs(s: seq<CPacket>, v: CRequestBatch) : int 
		requires (forall i :: i in s ==> CPacketIsValid(i))
		requires CRequestBatchIsValid(v)
		requires (forall p :: p in s ==> p.msg.CMessage_2b?)
		ensures var lr := CountMatchedValInReceived2bs(AbstractifySeq(s, AbstractifyCPacketToRslPacket), AbstractifyCRequestBatchToRequestBatch(v)); var cr := CCountMatchedValInReceived2bs(s, v); (cr) == (lr)
	{
		/* manually add */
		ghost var ls := AbstractifySeq(s, AbstractifyCPacketToRslPacket);
		ghost var lv := AbstractifyCRequestBatchToRequestBatch(v);

		if |s| == 0 then 
			0 
		else 
			/* manually add */
			lemma_seq_sub(s, AbstractifyCPacketToRslPacket, 0, |s|-1);
			ghost var r_prev := CCountMatchedValInReceived2bs(s[..|s|-1], v);
			ghost var ls_prev := AbstractifySeq(s[..|s|-1], AbstractifyCPacketToRslPacket);
			ghost var lr_prev := CountMatchedValInReceived2bs(ls_prev, lv);
			assert r_prev == lr_prev;
			ghost var cur := if s[|s| - 1].msg.val_2b == v then 1 else 0;
			ghost var s_last := s[|s|-1];
			assert CPacketIsValid(s_last);
			CCountMatchedValInReceived2bs(s[ .. |s| - 1], v) + if s[|s| - 1].msg.val_2b == v then 1 else 0
	}

	function method CIsWeakQuorumSendSame2b(vals: seq<CRequestBatch>, n: int) : bool 
		requires (forall i :: i in vals ==> CRequestBatchIsValid(i))
		ensures var lr := IsWeakQuorumSendSame2b(AbstractifySeq(vals, AbstractifyCRequestBatchToRequestBatch), n); var cr := CIsWeakQuorumSendSame2b(vals, n); (cr) == (lr)
	{
		(exists v :: v in vals && CCountMatchedInRequestBatches(vals, v) >= n)
	}

	function method CHasReceivedSame2bFromWeakQuorum(tup: CLearnerTuple, n: int) : bool 
		requires CLearnerTupleIsValid(tup)
		requires (forall p :: p in tup.received_2bs ==> p.msg.CMessage_2b?)
		ensures var lr := HasReceivedSame2bFromWeakQuorum(AbstractifyCLearnerTupleToLearnerTuple(tup), n); var cr := CHasReceivedSame2bFromWeakQuorum(tup, n); (cr) == (lr)
	{
		(exists p :: p in tup.received_2bs && CCountMatchedValInReceived2bs(tup.received_2bs, p.msg.val_2b) >= n)
	}

	lemma lemma_LearnerTupleIsUniqueSeq(tup:CLearnerTuple, ltup:LearnerTuple)
		requires CLearnerTupleIsValid(tup)
		requires ltup == AbstractifyCLearnerTupleToLearnerTuple(tup)
		ensures (forall i, j :: 0 <= i < |tup.received_2bs| && 0 <= j < |tup.received_2bs| && i != j ==> tup.received_2bs[i] != tup.received_2bs[j] && tup.received_2bs[i].src != tup.received_2bs[j].src) ==
				(forall i, j :: 0 <= i < |ltup.received_2bs| && 0 <= j < |ltup.received_2bs| && i != j ==> ltup.received_2bs[i] != ltup.received_2bs[j] && ltup.received_2bs[i].src != ltup.received_2bs[j].src)
	{
		var p2bs := tup.received_2bs;
		var lp2bs := ltup.received_2bs;
		assert lp2bs == AbstractifySeq(p2bs, AbstractifyCPacketToRslPacket);
		assert forall i :: i in p2bs ==> AbstractifyCPacketToRslPacket(i) in lp2bs;
	}

	lemma lemma_CLearnerTupleIsUniqueSeq(tup:CLearnerTuple)
		requires CLearnerTupleIsValid(tup)
		ensures 
			var lr := LearnerTupleIsUniqueSeq(AbstractifyCLearnerTupleToLearnerTuple(tup));
			var cr := (forall i, j :: 0 <= i < |tup.received_2bs| && 0 <= j < |tup.received_2bs| && i != j ==> tup.received_2bs[i] != tup.received_2bs[j] && tup.received_2bs[i].src != tup.received_2bs[j].src); 
			(cr) == (lr)
	{
		var ltup := AbstractifyCLearnerTupleToLearnerTuple(tup);
		lemma_LearnerTupleIsUniqueSeq(tup, ltup);
	}

	function method CLearnerTupleIsUniqueSeq(tup:CLearnerTuple) : bool
		requires CLearnerTupleIsValid(tup)
		ensures 
			var lr := LearnerTupleIsUniqueSeq(AbstractifyCLearnerTupleToLearnerTuple(tup));
			var cr := CLearnerTupleIsUniqueSeq(tup); 
			(cr) == (lr)
	{
		lemma_CLearnerTupleIsUniqueSeq(tup);
		(forall i, j :: 0 <= i < |tup.received_2bs| && 0 <= j < |tup.received_2bs| && i != j ==> tup.received_2bs[i] != tup.received_2bs[j] && tup.received_2bs[i].src != tup.received_2bs[j].src)
	}
	
	function method CLearnerTupleCorrect(tup: CLearnerTuple, bal: CBallot, opn: COperationNumber, c: CConfiguration) : bool 
		requires CLearnerTupleIsValid(tup)
		requires CBallotIsValid(bal)
		requires COperationNumberIsValid(opn)
		requires CConfigurationIsValid(c)
		ensures 
			var lr := LearnerTupleCorrect(AbstractifyCLearnerTupleToLearnerTuple(tup), AbstractifyCBallotToBallot(bal), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCConfigurationToLConfiguration(c)); 
			var cr := CLearnerTupleCorrect(tup, bal, opn, c); 
			(cr) == (lr)
	{
		|tup.received_2bs| <= |c.replica_ids| 
		&& 
		(forall p :: p in tup.received_2bs ==> p.msg.CMessage_2b? && p.msg.opn_2b == opn && p.msg.bal_2b == bal && p.src in c.replica_ids)
	}

	function method CLearnerStateCorrect(ls: CLearnerState, bal: CBallot, c: CConfiguration) : bool 
		requires CLearnerStateIsValid(ls)
		requires CBallotIsValid(bal)
		requires CConfigurationIsValid(c)
		ensures var lr := LearnerStateCorrect(AbstractifyCLearnerStateToLearnerState(ls), AbstractifyCBallotToBallot(bal), AbstractifyCConfigurationToLConfiguration(c)); var cr := CLearnerStateCorrect(ls, bal, c); (cr) == (lr)
	{
		(forall opn :: opn in ls ==> 
			&& CLearnerTupleCorrect(ls[opn], bal, opn, c)
			&& CLearnerTupleIsUniqueSeq(ls[opn]))
	}


  /** 7 + 2 */
  function method CLearnerInit(c: CReplicaConstants) : CLearner 
		requires CReplicaConstantsIsValid(c)
		ensures var l := CLearnerInit(c); CLearnerIsValid(l) && LLearnerInit(AbstractifyCLearnerToLLearner(l), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := c; 		
		var t2 := CBallot(0, 0); 		
		var t3 := map[]; 		
		CLearner(t1, t2, t3)
	}

  /** 48 + 4 + 12 */
  function method CLearnerProcess2b(s: CLearner, packet: CPacket) : CLearner 
		requires CLearnerIsValid(s)
		requires CPacketIsValid(packet)
		requires packet.msg.CMessage_2b?
		// requires CLearnerStateCorrect(s.unexecuted_learner_state, s.max_ballot_seen, s.constants.all.config)
		ensures var s' := CLearnerProcess2b(s, packet); CLearnerIsValid(s') && LLearnerProcess2b(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCPacketToRslPacket(packet))
	{
    /* manual annotations */
    lemma_AbstractifyMap_properties(s.unexecuted_learner_state, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, AbstractifyOperationNumberToCOperationNumber);
    ghost var ss := AbstractifyCLearnerToLLearner(s);
    ghost var p := AbstractifyCPacketToRslPacket(packet);

		// var t1 := 
			var m := 
				packet.msg; 			
			// var t1 := 
				var opn := 
					m.opn_2b; 				
				// var t1 := 
					if (packet.src !in s.constants.all.config.replica_ids) || (CBalLt(m.bal_2b, s.max_ballot_seen)) then 
						// var t1 := 
							s 						
						// t1 
					else 
						// var t1 := 
							if CBalLt(s.max_ballot_seen, m.bal_2b) then 
								// var t1 := 
									var tup' := 
										CLearnerTuple([packet]); 		
                  /* manual annotations */
                  assert CLearnerTupleIsAbstractable(tup');
                  var t' := LearnerTuple([p]);
                  assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

									// var t1 := 
										s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := map[opn:= tup'])									
									// t1; 								
								// t1 
							else 
								// var t1 := 
									if opn !in s.unexecuted_learner_state then 
										// var t1 := 
											var tup' := 
												CLearnerTuple([packet]); 		
                      /* manual annotations */ 
                      assert CLearnerTupleIsAbstractable(tup');
                      var t' := LearnerTuple([p]);
                      assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');	

											// var t1 := 
												s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']) 											
											// t1; 										
										// t1 
									else 
										// var t1 := 
											if (exists p :: p in s.unexecuted_learner_state[opn].received_2bs && p.src == packet.src) then 
												// var t1 := 
													s 												
												// t1 
											else 
												// var t1 := 
													var tup := 
														s.unexecuted_learner_state[opn]; 													
													// var t1 := 
														var tup' := 
															tup.(received_2bs := tup.received_2bs + [packet]); 	
                            /* manual annotations */
                            var t := ss.unexecuted_learner_state[opn];
                            var t' := t.(received_2bs := t.received_2bs + [p]);
                            assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

														// var t1 := 
															s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup'])														
		// 												t1; 													
		// 											t1; 												
		// 										t1; 										
		// 								t1; 								
		// 						t1; 						
		// 				t1; 				
		// 		t1; 			
		// 	t1; 		
		// t1
	}

  /** 12 + 3 */
  function method CLearnerForgetDecision(s: CLearner, opn: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CLearnerForgetDecision(s, opn); CLearnerIsValid(s') && LLearnerForgetDecision(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		// var t1 := 
		if opn in s.unexecuted_learner_state then 
		// var t1 := 
			s.(unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn)) 
		// t1 
		else 
		// var t1 := 
			s
		// t1; 		
		// t1
	}

  /** 7 + 3 */
  function method CLearnerForgetOperationsBefore(s: CLearner, ops_complete: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(ops_complete)
		ensures var s' := CLearnerForgetOperationsBefore(s, ops_complete); CLearnerIsValid(s') && LLearnerForgetOperationsBefore(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(ops_complete))
	{
		// var t1 := 
		s.(unexecuted_learner_state := 
		(map op | op in s.unexecuted_learner_state && op >= ops_complete :: s.unexecuted_learner_state[op]))	
		// t1
	}

  /************************** AutoMan Translation End ************************/
}
