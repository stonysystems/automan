include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "Constants.i.dfy"
include "Executor.i.dfy"
include "Acceptor.i.dfy"
include "../../Common/Collections/Maps.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"

module LiveByzRSL__Learner_i {
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Types_i
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__Executor_i
import opened LiveByzRSL__Acceptor_i
import opened Collections__Maps_i
import opened Collections__CountMatches_i
import opened Concrete_NodeIdentity_i
// 4

datatype LearnerTuple = LearnerTuple(received_2bs:seq<RslPacket>)
// datatype LearnerTuple = LearnerTuple(received_2bs:seq<NodeIdentity>, candidate_learned_value:seq<RequestBatch>)
type LearnerState = map<OperationNumber, LearnerTuple>

datatype LLearner = LLearner(
  constants:LReplicaConstants,
  max_ballot_seen:Ballot,
  unexecuted_learner_state:LearnerState
  )

function CountMatchedValInReceived2bs(s:seq<RslPacket>, v:RequestBatch) : int
  requires forall p :: p in s ==> p.msg.RslMessage_2b?
{
  if |s| == 0 then
    0
  else
    // CountMatchedValInReceived2bs(s[1..], v) + if s[0].msg.val_2b == v then 1 else 0
    CountMatchedValInReceived2bs(s[..|s|-1], v) + if s[|s|-1].msg.val_2b == v then 1 else 0
}

predicate IsWeakQuorumSendSame2b(vals:seq<RequestBatch>, n:int)
{
  exists v :: v in vals && CountMatchedInRequestBatches(vals, v) >= n
}

predicate HasReceivedSame2bFromWeakQuorum(tup:LearnerTuple, n:int)
  requires forall p :: p in tup.received_2bs ==> p.msg.RslMessage_2b?
{
  exists p :: p in tup.received_2bs && CountMatchedValInReceived2bs(tup.received_2bs, p.msg.val_2b) >= n
}

predicate LearnerTupleIsUniqueSeq(tup:LearnerTuple)
{
  && (forall i,j :: 0 <= i < |tup.received_2bs| && 0 <= j < |tup.received_2bs| && i != j 
                  ==> tup.received_2bs[i] != tup.received_2bs[j] && tup.received_2bs[i].src != tup.received_2bs[j].src)
}

predicate LearnerTupleCorrect(tup:LearnerTuple, bal:Ballot, opn:OperationNumber, c:LConfiguration)
{
  && |tup.received_2bs| <= |c.replica_ids|
  && (forall p :: p in tup.received_2bs ==> 
              && p.msg.RslMessage_2b?
              && p.msg.opn_2b == opn
              && p.msg.bal_2b == bal
              && p.src in c.replica_ids)
}

predicate LearnerStateCorrect(ls:LearnerState, bal:Ballot, c:LConfiguration)
{
  (forall opn :: opn in ls ==> 
    && LearnerTupleCorrect(ls[opn], bal, opn, c)
    && LearnerTupleIsUniqueSeq(ls[opn]))
}

predicate LLearnerInit(l:LLearner, c:LReplicaConstants)
{
  && l.constants == c
  && l.max_ballot_seen == Ballot(0,0)
  && l.unexecuted_learner_state == map[]
}

predicate LLearnerProcess2b(s:LLearner, s':LLearner, packet:RslPacket)
  requires packet.msg.RslMessage_2b?
  // requires LearnerStateCorrect(s.unexecuted_learner_state, s.max_ballot_seen, s.constants.all.config)
{
  var m := packet.msg;
  var opn := m.opn_2b;
  if packet.src !in s.constants.all.config.replica_ids || BalLt(m.bal_2b, s.max_ballot_seen) then
    s' == s
  else if BalLt(s.max_ballot_seen, m.bal_2b) then
    var tup' := LearnerTuple([packet]);
    s' == s.(max_ballot_seen := m.bal_2b,
             unexecuted_learner_state := map[opn := tup'])
  else if opn !in s.unexecuted_learner_state then
    var tup' := LearnerTuple([packet]);
    s' == s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup'])
  else if 
    // packet.src in s.unexecuted_learner_state[opn].received_2bs 
    (exists p :: p in s.unexecuted_learner_state[opn].received_2bs && p.src == packet.src)
  then
    s' == s
  else
    var tup := s.unexecuted_learner_state[opn];
    var tup' := tup.(received_2bs := tup.received_2bs + [packet]);
    s' == s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup'])
}

predicate LLearnerForgetDecision(s:LLearner, s':LLearner, opn:OperationNumber)
{
  if opn in s.unexecuted_learner_state then
    // var ns := s.(unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn));
    // assert check(s, ns, opn, packet.src);
    s' == s.(unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn))
  else
    // var ns := s;
    // assert check(s, ns, opn, packet.src);
    s' == s
}

predicate LLearnerForgetOperationsBefore(s:LLearner, s':LLearner, ops_complete:OperationNumber)
{
  s' == s.(unexecuted_learner_state := (map op | op in s.unexecuted_learner_state && op >= ops_complete :: s.unexecuted_learner_state[op]))
}

} 
