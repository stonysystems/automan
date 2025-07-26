include "AppInterface.i.dfy"
include "../../Protocol/RSL/Learner.i.dfy"
include "CConstants.i.dfy"
include "ExecutorImpl.i.dfy"
include "../../Protocol/RSL/Learner.i.dfy"

module LiveRSL__LearnerModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveRSL__AppInterface_i
  import opened LiveRSL__CMessage_i
  import opened LiveRSL__CMessageRefinements_i
  import opened LiveRSL__CTypes_i
  import opened LiveRSL__Environment_i
  import opened LiveRSL__ExecutorModel_i
  import opened LiveRSL__Learner_i
  import opened LiveRSL__Message_i
  import opened LiveRSL__PacketParsing_i
  import opened LiveRSL__ConstantsState_i
  import opened LiveRSL__Types_i
  import opened Collections__Maps_i
  import opened Collections__Sets_i
  import opened Common__NodeIdentity_i
  import opened Common__SeqIsUnique_i
  import opened Common__SeqIsUniqueDef_i
  import opened Common__UdpClient_i
  import opened Concrete_NodeIdentity_i
  import opened GenericRefinement_i

  /************************** AutoMan Translation ************************/

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
		ensures var s' := CLearnerProcess2b(s, packet); CLearnerIsValid(s') && LLearnerProcess2b(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCPacketToRslPacket(packet))
	{
    /* manual annotations */
    lemma_AbstractifyMap_properties(s.unexecuted_learner_state, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, AbstractifyOperationNumberToCOperationNumber);
    ghost var ss := AbstractifyCLearnerToLLearner(s);
    ghost var p := AbstractifyCPacketToRslPacket(packet);

		var t1 := var m := packet.msg; 
    var t1 := var opn := m.opn_2b; 
    var t1 := 
      if packet.src !in s.constants.all.config.replica_ids || CBalLt(m.bal_2b, s.max_ballot_seen) then 
        var t1 := s; 
        t1 
      else 
        var t1 := 
          if CBalLt(s.max_ballot_seen, m.bal_2b) then 
            var t1 := var tup' := CLearnerTuple({packet.src}, m.val_2b); 
            /* manual annotations */
            assert CLearnerTupleIsAbstractable(tup');
            var t' := LearnerTuple({p.src}, p.msg.val_2b);
            assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

            var t1 := s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := map[opn := tup']); 
            // var t1 := s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := map[opn: tup']); 
            t1; 
            t1 
          else 
            var t1 := 
              if opn !in s.unexecuted_learner_state then 
                var t1 := 
                  var tup' := CLearnerTuple({packet.src}, m.val_2b);
                  /* manual annotations */ 
                  assert CLearnerTupleIsAbstractable(tup');
                  var t' := LearnerTuple({p.src}, p.msg.val_2b);
                  assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

                  var t1 := s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']); 
                  t1; 
                t1 
              else 
                var t1 := 
                  if packet.src in s.unexecuted_learner_state[opn].received_2b_message_senders then 
                    var t1 := s; 
                    t1 
                  else 
                    var t1 := 
                      var tup := s.unexecuted_learner_state[opn]; 
                      var t1 := var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src});
                        /* manual annotations */
                        var t := ss.unexecuted_learner_state[opn as int];
                        var t' := t.(received_2b_message_senders := t.received_2b_message_senders + {p.src});
                        assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

                      var t1 := s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']); 
                    t1; 
                  t1; 
                t1; 
              t1; 
            t1; 
          t1; 
        t1; 
      t1; 		
		t1
	}

  /** 12 + 3 */
  function method CLearnerForgetDecision(s: CLearner, opn: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CLearnerForgetDecision(s, opn); CLearnerIsValid(s') && LLearnerForgetDecision(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		var t1 := 
    if opn in s.unexecuted_learner_state then 
      var t1 := 
      s.(unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn)); 
      t1 
    else 
      var t1 := s; 
      t1; 		
		t1
	}

  /** 7 + 3 */
  function method CLearnerForgetOperationsBefore(s: CLearner, ops_complete: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(ops_complete)
		ensures var s' := CLearnerForgetOperationsBefore(s, ops_complete); CLearnerIsValid(s') && LLearnerForgetOperationsBefore(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(ops_complete))
	{
		var t1 := s.(unexecuted_learner_state := 
      (map op | op in s.unexecuted_learner_state && op >= ops_complete :: s.unexecuted_learner_state[op])
    ); 		
		t1
	}

  /************************** AutoMan Translation End ************************/
}
