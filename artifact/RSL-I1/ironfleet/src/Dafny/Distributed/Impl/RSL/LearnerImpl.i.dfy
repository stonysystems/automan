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

  /** 9 lines manual code for I1 */
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

		var m := packet.msg; 
    var opn := m.opn_2b; 
    // var t1 := 
      if packet.src !in s.constants.all.config.replica_ids || CBalLt(m.bal_2b, s.max_ballot_seen) then 
        s
      else 
        // var t1 := 
          if CBalLt(s.max_ballot_seen, m.bal_2b) then 
            var tup' := CLearnerTuple({packet.src}, m.val_2b); 
            /* manual annotations */
            assert CLearnerTupleIsAbstractable(tup');
            var t' := LearnerTuple({p.src}, p.msg.val_2b);
            assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

            s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := map[opn := tup']) 
            // var t1 := s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := map[opn: tup']); 
            // t1; 
            // t1 
          else 
            // var t1 := 
              if opn !in s.unexecuted_learner_state then 
                // var t1 := 
                  var tup' := CLearnerTuple({packet.src}, m.val_2b);
                  /* manual annotations */ 
                  assert CLearnerTupleIsAbstractable(tup');
                  var t' := LearnerTuple({p.src}, p.msg.val_2b);
                  assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

                  s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup'])
                //   t1; 
                // t1 
              else 
                // var t1 := 
                  if packet.src in s.unexecuted_learner_state[opn].received_2b_message_senders then 
                    s
                    // t1
                  else 
                    // var t1 := 
                      var tup := s.unexecuted_learner_state[opn]; 
                      var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src});
                      /* manual annotations */
                      var t := ss.unexecuted_learner_state[opn as int];
                      var t' := t.(received_2b_message_senders := t.received_2b_message_senders + {p.src});
                      assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

                      s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup'])
    //                 t1; 
    //               t1; 
    //             t1; 
    //           t1; 
    //         t1; 
    //       t1; 
    //     t1; 
    //   t1; 		
		// t1
	}

  // function method CLearnerProcess2b(s: CLearner, packet: CPacket) : CLearner 
	// 	requires CLearnerIsValid(s)
	// 	requires CPacketIsValid(packet)
	// 	requires packet.msg.CMessage_2b?
	// 	ensures var s' := CLearnerProcess2b(s, packet); CLearnerIsValid(s') && LLearnerProcess2b(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCPacketToRslPacket(packet))
	// {
  //   /* manual annotations */
  //   lemma_AbstractifyMap_properties(s.unexecuted_learner_state, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, AbstractifyOperationNumberToCOperationNumber);
  //   ghost var ss := AbstractifyCLearnerToLLearner(s);
  //   ghost var p := AbstractifyCPacketToRslPacket(packet);

	// 	var t1 := var m := packet.msg; 
  //   var t1 := var opn := m.opn_2b; 
  //   var t1 := 
  //     if packet.src !in s.constants.all.config.replica_ids || CBalLt(m.bal_2b, s.max_ballot_seen) then 
  //       var t1 := s; 
  //       t1 
  //     else 
  //       var t1 := 
  //         if CBalLt(s.max_ballot_seen, m.bal_2b) then 
  //           var t1 := var tup' := CLearnerTuple({packet.src}, m.val_2b); 
  //           /* manual annotations */
  //           assert CLearnerTupleIsAbstractable(tup');
  //           var t' := LearnerTuple({p.src}, p.msg.val_2b);
  //           assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

  //           var t1 := s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := map[opn := tup']); 
  //           // var t1 := s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := map[opn: tup']); 
  //           t1; 
  //           t1 
  //         else 
  //           var t1 := 
  //             if opn !in s.unexecuted_learner_state then 
  //               var t1 := 
  //                 var tup' := CLearnerTuple({packet.src}, m.val_2b);
  //                 /* manual annotations */ 
  //                 assert CLearnerTupleIsAbstractable(tup');
  //                 var t' := LearnerTuple({p.src}, p.msg.val_2b);
  //                 assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

  //                 var t1 := s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']); 
  //                 t1; 
  //               t1 
  //             else 
  //               var t1 := 
  //                 if packet.src in s.unexecuted_learner_state[opn].received_2b_message_senders then 
  //                   var t1 := s; 
  //                   t1 
  //                 else 
  //                   var t1 := 
  //                     var tup := s.unexecuted_learner_state[opn]; 
  //                     var t1 := var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src});
  //                       /* manual annotations */
  //                       var t := ss.unexecuted_learner_state[opn as int];
  //                       var t' := t.(received_2b_message_senders := t.received_2b_message_senders + {p.src});
  //                       assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

  //                     var t1 := s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']); 
  //                   t1; 
  //                 t1; 
  //               t1; 
  //             t1; 
  //           t1; 
  //         t1; 
  //       t1; 
  //     t1; 		
	// 	t1
	// }

  /** 3 lines manual code for I1 */
  function method CLearnerForgetDecision(s: CLearner, opn: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CLearnerForgetDecision(s, opn); CLearnerIsValid(s') && LLearnerForgetDecision(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		// var t1 := 
      if opn in s.unexecuted_learner_state then 
        s.(unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn))
        // t1 
      else 
        s 
      // t1; 		
		// t1
	}

  function method CLearnerForgetOperationsBefore(s: CLearner, ops_complete: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(ops_complete)
		ensures var s' := CLearnerForgetOperationsBefore(s, ops_complete); CLearnerIsValid(s') && LLearnerForgetOperationsBefore(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(ops_complete))
	{
		s.(unexecuted_learner_state := 
      (map op | op in s.unexecuted_learner_state && op >= ops_complete :: s.unexecuted_learner_state[op])
    )		
	}

  /************************** AutoMan Translation End ************************/
  /* ----------------------------------------- */

  // datatype CLearner =
  //   CLearner
  //   (
  //     constants : CReplicaConstants ,
  //     max_ballot_seen : CBallot ,
  //     unexecuted_learner_state : CLearnerState
  //   )

  // predicate CLearnerIsValid(
  //   s : CLearner)

  // {
  //   CLearnerIsAbstractable(s)
  //   &&
  //   CReplicaConstantsIsValid(s.constants)
  //   &&
  //   CBallotIsValid(s.max_ballot_seen)
  //   &&
  //   CLearnerStateIsValid(s.unexecuted_learner_state)
  // }

  // predicate CLearnerIsAbstractable(
  //   s : CLearner)

  // {
  //   CReplicaConstantsIsAbstractable(s.constants)
  //   &&
  //   CBallotIsAbstractable(s.max_ballot_seen)
  //   &&
  //   CLearnerStateIsAbstractable(s.unexecuted_learner_state)
  // }

  // function AbstractifyCLearnerToLLearner(
  //   s : CLearner) : LLearner
  //   requires CLearnerIsAbstractable(s)
  // {
  //   var constants       := AbstractifyCReplicaConstantsToLReplicaConstants(s.constants);
  //   var ballot          := AbstractifyCBallotToBallot(s.max_ballot_seen);
  //   var unexecuted_ops  := AbstractifyCLearnerStateToLearnerState(s.unexecuted_learner_state);
  //   LLearner(constants, ballot, unexecuted_ops)
  //   /* Timeout */
  //   // LLearner(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_ballot_seen), AbstractifyCLearnerStateToLearnerState(s.unexecuted_learner_state))
  // }

  // function method {:opaque} CLearnerInit(
  //   c : CReplicaConstants) : CLearner
  //   requires CReplicaConstantsIsValid(c)
  //   ensures var l := CLearnerInit(c); CLearnerIsValid(l) && LLearnerInit(AbstractifyCLearnerToLLearner(l), AbstractifyCReplicaConstantsToLReplicaConstants(c))
  // {
  //   CLearner(constants := c, max_ballot_seen := CBallot(0, 0), unexecuted_learner_state := map[])
  // }

  /* Axiom Lemma */
  // function method {:opaque} CLearnerProcess2b(
  //   s : CLearner ,
  //   packet : CPacket) : CLearner
  //   requires packet.msg.CMessage_2b?
  //   requires CLearnerIsValid(s)
  //   requires CPacketIsValid(packet)
  //   ensures var s' := CLearnerProcess2b(s, packet); CLearnerIsValid(s') && LLearnerProcess2b(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCPacketToRslPacket(packet))
  // {
  //   lemma_AbstractifyMap_properties(s.unexecuted_learner_state, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, AbstractifyOperationNumberToCOperationNumber);
  //   ghost var ss := AbstractifyCLearnerToLLearner(s);
  //   ghost var p := AbstractifyCPacketToRslPacket(packet);
  //   var m := packet.msg;
  //   var opn := m.opn_2b;

  //   var s' :=
  //     if packet.src !in s.constants.all.config.replica_ids || CBalLt(m.bal_2b, s.max_ballot_seen)
  //     then
  //       s
  //     else
  //       if CBalLt(s.max_ballot_seen, m.bal_2b)
  //       then
  //         var tup' := CLearnerTuple({packet.src}, m.val_2b);

  //         assert CLearnerTupleIsAbstractable(tup');
  //         var t' := LearnerTuple({p.src}, p.msg.val_2b);
  //         assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

  //         s.(
  //     max_ballot_seen := m.bal_2b,
  //     unexecuted_learner_state := map[opn := tup']
  //   )
  //       else
  //         if opn !in s.unexecuted_learner_state
  //         then
  //           var tup' := CLearnerTuple({packet.src}, m.val_2b);

  //           assert CLearnerTupleIsAbstractable(tup');
  //           var t' := LearnerTuple({p.src}, p.msg.val_2b);
  //           assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');

  //           s.(
  //     unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']
  //   )
  //         else
  //           if packet.src in s.unexecuted_learner_state[opn].received_2b_message_senders
  //           then
  //             s
  //           else
  //             var tup := s.unexecuted_learner_state[opn];
  //             var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src});

  //             var t := ss.unexecuted_learner_state[opn as int];
  //             var t' := t.(received_2b_message_senders := t.received_2b_message_senders + {p.src});
  //             assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');


  //             s.(
  //     unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']
  //   );

  //   // CLearnerProcess2bHelper(s, packet, s');
  //   s'
  // }

  // function method {:opaque} CLearnerForgetDecision(
  //   s : CLearner ,
  //   opn : COperationNumber) : CLearner
  //   requires CLearnerIsValid(s)
  //   requires COperationNumberIsValid(opn)
  //   ensures var s' := CLearnerForgetDecision(s, opn); CLearnerIsValid(s') && LLearnerForgetDecision(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(opn))
  // {
  //   if opn in s.unexecuted_learner_state
  //   then
  //     s.(
  //     unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn)
  //   )
  //   else
  //     s
  // }

  // function method {:opaque} CLearnerForgetOperationsBefore(
  //   s : CLearner ,
  //   ops_complete : COperationNumber) : CLearner
  //   requires CLearnerIsValid(s)
  //   requires COperationNumberIsValid(ops_complete)
  //   ensures var s' := CLearnerForgetOperationsBefore(s, ops_complete); CLearnerIsValid(s') && LLearnerForgetOperationsBefore(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(ops_complete))
  // {
  //   s.(
  //     unexecuted_learner_state := (map op | op in s.unexecuted_learner_state && op >= ops_complete :: s.unexecuted_learner_state[op])
  //   )
  // }

  /* ----------------------------------------- */

  // predicate LearnerState_CommonPreconditions(learner:CLearner)
  // {
  //   CLearnerIsValid(learner)
  // }

  // predicate LearnerState_Process2b__Preconditions(learner:CLearner, executor:CExecutor, packet:CPacket)
  // {
  //   && LearnerState_CommonPreconditions(learner)
  //   && CExecutor_CommonPreconditions(executor)
  //   && CPacketIsAbstractable(packet)
  //   && packet.msg.CMessage_2b?
  // }

  // predicate LearnerState_ForgetOperationsBefore__Preconditions(learner:CLearner, opn:COperationNumber)
  // {
  //   && LearnerState_CommonPreconditions(learner)
  // }

  // lemma {:axiom} CLearnerProcess2bHelper(learner:CLearner, packet:CPacket, learner':CLearner)
  //   requires packet.msg.CMessage_2b?
  //   requires CBallotIsValid(packet.msg.bal_2b)
  //   requires CLearnerIsValid(learner)
  //   requires CPacketIsValid(packet)
  //   ensures CLearnerIsValid(learner')
  //   // ensures LLearnerProcess2b(
  //   //           AbstractifyCLearnerToLLearner(learner),
  //   //           AbstractifyCLearnerToLLearner(learner'),
  //   //           AbstractifyCPacketToRslPacket(packet)
  //   //         )

  
  // method CLearnerProcess2b_1(learner:CLearner, packet:CPacket) returns (learner':CLearner)
  //   requires packet.msg.CMessage_2b?
  //   requires CBallotIsValid(packet.msg.bal_2b)
  //   requires CLearnerIsValid(learner)
  //   requires CPacketIsValid(packet)
  //   ensures CLearnerIsValid(learner')
  //   // ensures LLearnerProcess2b(
  //   //           AbstractifyCLearnerToLLearner(learner),
  //   //           AbstractifyCLearnerToLLearner(learner'),
  //   //           AbstractifyCPacketToRslPacket(packet)
  //   //         )
  // {
  //   ghost var s := AbstractifyCLearnerToLLearner(learner);
  //   ghost var p := AbstractifyCPacketToRslPacket(packet);
  //   var v := packet.msg.val_2b;
  //   var msg := packet.msg;
  //   var opn := msg.opn_2b;
  //   if packet.src !in learner.constants.all.config.replica_ids || CBalLt(msg.bal_2b, learner.max_ballot_seen){
  //     learner' := learner;
  //   } else if CBalLt(learner.max_ballot_seen, msg.bal_2b){
  //     var tup' := CLearnerTuple({packet.src}, v);
  //     var t' := LearnerTuple({p.src}, p.msg.val_2b);
  //     assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');
  //     learner' :=
  //       learner.(
  //       max_ballot_seen := msg.bal_2b,
  //       unexecuted_learner_state := map[opn := tup']);
  //   } else if opn !in learner.unexecuted_learner_state {
  //     var tup' := CLearnerTuple({packet.src}, v);
  //     var t' := LearnerTuple({p.src}, p.msg.val_2b);
  //     assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');
  //     learner' := learner.(unexecuted_learner_state := learner.unexecuted_learner_state[opn := tup']);
  //   } else if packet.src in learner.unexecuted_learner_state[opn].received_2b_message_senders {
  //     learner' := learner;
  //   } else {
  //     var tup := learner.unexecuted_learner_state[opn];
  //     var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src});
  //     var t := s.unexecuted_learner_state[opn as int];
  //     var t' := t.(received_2b_message_senders := t.received_2b_message_senders + {p.src});
  //     assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');
  //     learner' := learner.(unexecuted_learner_state := learner.unexecuted_learner_state[opn := tup']);
  //   }

  //   CLearnerProcess2bHelper(learner, packet, learner');
  // }
  
  
// method CLearnerProcess2b_1(learner:CLearner, packet:CPacket) returns (learner':CLearner)
//   requires packet.msg.CMessage_2b?
//   requires CBallotIsValid(packet.msg.bal_2b)
//   requires CLearnerIsValid(learner)
//   requires CPacketIsValid(packet)
//   ensures CLearnerIsValid(learner')
//   ensures LLearnerProcess2b(
//           AbstractifyCLearnerToLLearner(learner),
//           AbstractifyCLearnerToLLearner(learner'),
//           AbstractifyCPacketToRslPacket(packet)
//   )
// {
//   lemma_AbstractifyMap_properties(learner.unexecuted_learner_state, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, AbstractifyOperationNumberToCOperationNumber);
//   ghost var s := AbstractifyCLearnerToLLearner(learner);
//   ghost var p := AbstractifyCPacketToRslPacket(packet);
//   var v := packet.msg.val_2b;
//   var msg := packet.msg;
//   var opn := msg.opn_2b;
//   if packet.src !in learner.constants.all.config.replica_ids || CBalLt(msg.bal_2b, learner.max_ballot_seen){
//     learner' := learner;
//   } else if CBalLt(learner.max_ballot_seen, msg.bal_2b){
//     var tup' := CLearnerTuple({packet.src}, v);
//     assert CLearnerTupleIsAbstractable(tup');
//     var t' := LearnerTuple({p.src}, p.msg.val_2b);
//     assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');
//     learner' :=
//             learner.(
//                 max_ballot_seen := msg.bal_2b,
//                 unexecuted_learner_state := map[opn := tup']);
//     // assert CReplicaConstantsIsValid(learner'.constants);
//     // assert CBallotIsValid(learner'.max_ballot_seen);
//     // assert CLearnerStateIsAbstractable(learner'.unexecuted_learner_state);
//     // assert forall i :: i in learner'.unexecuted_learner_state ==> CLearnerTupleIsAbstractable(learner'.unexecuted_learner_state[i]);
//     // assert CLearnerIsAbstractable(learner');
//     // assert CLearnerIsValid(learner');
//     // assert LLearnerProcess2b(
//     //       AbstractifyCLearnerToLLearner(learner),
//     //       AbstractifyCLearnerToLLearner(learner'),
//     //       AbstractifyCPacketToRslPacket(packet)
//     // );
//   } else if opn !in learner.unexecuted_learner_state {
//     var tup' := CLearnerTuple({packet.src}, v);
//     assert CLearnerTupleIsAbstractable(tup');
//     var t' := LearnerTuple({p.src}, p.msg.val_2b);
//     assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');
//     learner' := learner.(unexecuted_learner_state := learner.unexecuted_learner_state[opn := tup']);
//     // assert CLearnerIsValid(learner');
//     // assert LLearnerProcess2b(
//     //       AbstractifyCLearnerToLLearner(learner),
//     //       AbstractifyCLearnerToLLearner(learner'),
//     //       AbstractifyCPacketToRslPacket(packet)
//     // );
//   } else if packet.src in learner.unexecuted_learner_state[opn].received_2b_message_senders {
//     learner' := learner;
//     // assert CLearnerIsValid(learner');
//     // assert LLearnerProcess2b(
//     //       AbstractifyCLearnerToLLearner(learner),
//     //       AbstractifyCLearnerToLLearner(learner'),
//     //       AbstractifyCPacketToRslPacket(packet)
//     // );
//   } else {
//     var tup := learner.unexecuted_learner_state[opn];
//     var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src});
//     var t := s.unexecuted_learner_state[opn as int];
//     var t' := t.(received_2b_message_senders := t.received_2b_message_senders + {p.src});
//     assert t' == AbstractifyCLearnerTupleToLearnerTuple(tup');
//     learner' := learner.(unexecuted_learner_state := learner.unexecuted_learner_state[opn := tup']);
//     // assert CLearnerIsValid(learner');
//     // assert LLearnerProcess2b(
//     //       AbstractifyCLearnerToLLearner(learner),
//     //       AbstractifyCLearnerToLLearner(learner'),
//     //       AbstractifyCPacketToRslPacket(packet)
//     // );
//   }
//   // CLearnerProcess2bHelper(learner, packet, learner');
// }

}
