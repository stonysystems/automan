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
// import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Environment_i
import opened LiveRSL__ExecutorModel_i
import opened LiveRSL__Learner_i
// import opened LiveRSL__LearnerState_i
import opened LiveRSL__Message_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__Types_i
import opened Collections__Maps_i
import opened Collections__Sets_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUnique_i
import opened Common__SeqIsUniqueDef_i
import opened Common__NetClient_i
import opened Concrete_NodeIdentity_i
import opened GenericRefinement_i

/************************** AutoMan Translation ************************/
  datatype CLearner = 
	CLearner(
		constants: CReplicaConstants, 
		max_ballot_seen: CBallot, 
		unexecuted_learner_state: CLearnerState
	)

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

	predicate CLearnerIsAbstractable(s: CLearner) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CBallotIsAbstractable(s.max_ballot_seen) 
		&& 
    CLearnerStateIsAbstractable(s.unexecuted_learner_state)
		// CearnerStateIsAbstractable(s.unexecuted_learner_state)
	}

	function AbstractifyCLearnerToLLearner(s: CLearner) : LLearner 
		requires CLearnerIsAbstractable(s)
	{
		LLearner(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_ballot_seen), AbstractifyCLearnerStateToLearnerState(s.unexecuted_learner_state))
	}

  function method CLearnerInit(c: CReplicaConstants) : CLearner 
		requires CReplicaConstantsIsValid(c)
		ensures var l := CLearnerInit(c); CLearnerIsValid(l) && LLearnerInit(AbstractifyCLearnerToLLearner(l), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := c; 		
		var t2 := CBallot(0, 0); 		
		var t3 := map[]; 		
		CLearner(t1, t2, t3)
	}

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

  function method CLearnerForgetDecision(s: CLearner, opn: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CLearnerForgetDecision(s, opn); CLearnerIsValid(s') && LLearnerForgetDecision(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		var t1 := if opn in s.unexecuted_learner_state then var t1 := s.(unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn)); t1 else var t1 := s; t1; 		
		t1
	}

  function method CLearnerForgetOperationsBefore(s: CLearner, ops_complete: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(ops_complete)
		ensures var s' := CLearnerForgetOperationsBefore(s, ops_complete); CLearnerIsValid(s') && LLearnerForgetOperationsBefore(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(ops_complete))
	{
		var t1 := s.(unexecuted_learner_state := 
      (map op | op in s.unexecuted_learner_state && op >= ops_complete :: s.unexecuted_learner_state[op])
      // [Printer for ... hasn't been implemented.]
    ); 		
		t1
	}

  /************************** AutoMan Translation End ************************/
// datatype CLearnerState =
//   CLearnerState(
//     rcs:CReplicaConstants,
//     max_ballot_seen:CBallot,
//     unexecuted_learner_state:CLearnerStateMap
//     )

//     // sendDecision:bool,
//     // opn:COperationNumber,
//     // recv2b:bool,
//     // recvCp:CPacket

// function CLearnerStateVaild(s:CLearnerState) : bool
// {
//   && LearnerState_IsAbstractable(s)
//   && (forall o :: o in s.unexecuted_learner_state ==> CLearnerTupleIsValid(s.unexecuted_learner_state[o]))
//    && CReplicaConstansValid(s.rcs)
//    && CBallotValid(s.max_ballot_seen)
//    && ReplicaConstantsStateIsAbstractable(s.rcs)
// }

// predicate LearnerState_IsAbstractable(learner:CLearnerState)
// {
//   && CBallotIsAbstractable(learner.max_ballot_seen)
//   && ReplicaConstantsStateIsAbstractable(learner.rcs)
//   && CLearnerTuplesAreAbstractable(learner.unexecuted_learner_state)
// }

// function AbstractifyLearnerStateToLLearner(learner:CLearnerState) : LLearner
//   requires LearnerState_IsAbstractable(learner)
// {
//   var rcs := AbstractifyReplicaConstantsStateToLReplicaConstants(learner.rcs);
//   var ballot := AbstractifyCBallotToBallot(learner.max_ballot_seen);
//   var unexecuted_ops := AbstractifyCLearnerTuplesToLearnerTuples(learner.unexecuted_learner_state);
//   LLearner(rcs, ballot, unexecuted_ops)
// }

// predicate LearnerState_CommonPreconditions(learner:CLearnerState)
// {
//   CLearnerStateVaild(learner)
// }

// predicate LearnerState_Process2b__Preconditions(learner:CLearnerState, executor:ExecutorState, packet:CPacket)
// {
//   && LearnerState_CommonPreconditions(learner)
//   && ExecutorState_CommonPreconditions(executor)
//   && CPacketIsAbstractable(packet)
//   && packet.msg.CMessage_2b?
// }

// predicate LearnerState_ForgetOperationsBefore__Preconditions(learner:CLearnerState, opn:COperationNumber)
// {
//   && LearnerState_CommonPreconditions(learner)
//   // && COperationNumberIsAbstractable(opn)
// }

// // predicate Eq_LLearner(x:LLearner, y:LLearner)
// // {
// //   && x.constants == y.constants
// //   && x.max_ballot_seen == y.max_ballot_seen
// //   && x.unexecuted_learner_state == y.unexecuted_learner_state
// // }

// method CLearnerInit(rcs:CReplicaConstants) returns (learner:CLearnerState)
// requires ReplicaConstantsStateIsAbstractable(rcs)
//   requires CReplicaConstansValid(rcs)
//  ensures learner.rcs == rcs
//   ensures CLearnerStateVaild(learner)
//   ensures LLearnerInit(AbstractifyLearnerStateToLLearner(learner), AbstractifyReplicaConstantsStateToLReplicaConstants(learner.rcs))
// {
//   // learner.rcs := rcs;
//   // learner.max_ballot_seen := CBallot(0,0);
//   // learner.unexecuted_learner_state := map[];
//   learner := CLearnerState(
//     rcs,
//     CBallot(0,0),
//     map[]
//   );
// }

// method CLearnerProcess2b(learner:CLearnerState, packet:CPacket) returns (learner':CLearnerState)
//   requires packet.msg.CMessage_2b?
// {
//   var msg := packet.msg;
//   var opn := msg.opn_2b;
//   if packet.src !in learner.rcs.all.config.replica_ids || CBalLt(msg.bal_2b, learner.max_ballot_seen){
//     learner' := learner;
//   } else if CBalLt(learner.max_ballot_seen, msg.bal_2b){
//     var tup' := CLearnerTuple({packet.src}, msg.val_2b);
//     learner' :=
//             learner.(
//                 max_ballot_seen := msg.bal_2b,
//                 unexecuted_learner_state := map[opn := tup']);
//   } else if opn !in learner.unexecuted_learner_state {
//     var tup' := CLearnerTuple({packet.src}, msg.val_2b);
//     learner' := learner.(unexecuted_learner_state := learner.unexecuted_learner_state[opn := tup']);
//   } else if packet.src in learner.unexecuted_learner_state[opn].received_2b_message_senders {
//     learner' := learner;
//   } else {
//     var tup := learner.unexecuted_learner_state[opn];
//     var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src});
//     learner' := learner.(unexecuted_learner_state := learner.unexecuted_learner_state[opn := tup']);
//   }
// }

// method CLearnerForgetDecision(learner:CLearnerState, opn:COperationNumber) returns (learner':CLearnerState)
// {
//    if (opn in learner.unexecuted_learner_state){
//     learner' := learner.(unexecuted_learner_state := RemoveElt(learner.unexecuted_learner_state, opn));
//    } else {
//     learner' := learner;
//    }
// }

// method CLearnerForgetOperationsBefore(learner:CLearnerState, ops_complete:COperationNumber) returns (learner':CLearnerState)
// {
//   learner' := learner.(unexecuted_learner_state := (map op | op in learner.unexecuted_learner_state && op >= ops_complete :: learner.unexecuted_learner_state[op]));
// }

} 
