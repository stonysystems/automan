# AutoMan

AutoMan is a tool for generating distributed system implementations from Dafny protocol specifications.

# Building

``` shell
opam switch create ./ 4.14.0
eval $(opam env)
opam install dune menhir ppx_deriving yojson
opam install . --deps-only
dune build
```

We use Menhir to implement the parser for the Dafny language. However, due to the limitations of LL(1) parsing, it cannot fully support all features of Dafny, which results in the warning:
```
Warning: 31 states have shift/reduce conflicts.
Warning: 61 shift/reduce conflicts were arbitrarily resolved.
```

# Quick Run

We provide two sets of specifications, both adapted from 
[IronFleet](https://github.com/microsoft/Ironclad/tree/main/ironfleet):
1. Multi-Paxos (rsl), available at  `./asset/spec/RSL`.
2. Key-Value Store (kv), available at `./asset/spec/KV`.
3. BadExamples (bad), available at `./asset/spec/BadExamples`, demonstrates cases that would fail AutoMan's checks.

The necessary annotations (explained below) are available at `./asset/annotations`.

Run `bash run.sh [rsl | kv | bad]` to apply the translation.

The generated codes can be found in `./asset/impl`.

# Usage

Here, we introduce how to write specifications in Dafny 3.X that can be translated by AutoMan.

## Name Remapping

For each mathematical model defined in the specification, AutoMan generates corresponding concrete versions for use in the implementation, along with a proof skeleton to help link them together.

Example:
```
datatype LAcceptor = LAcceptor(
    constants:LReplicaConstants,
    max_bal:Ballot,
    votes:Votes,
    last_checkpointed_operation:seq<OperationNumber>,
    log_truncation_point:OperationNumber
)
```
->
```
datatype CAcceptor = 
CAcceptor(
    constants: CReplicaConstants, 
    max_bal: CBallot, 
    votes: CVotes, 
    last_checkpointed_operation: seq<COperationNumber>, 
    log_truncation_point: COperationNumber
)

predicate CAcceptorIsValid(s: CAcceptor) { ... ... }

predicate CAcceptorIsAbstractable(s: CAcceptor) { ... ... }

function AbstractifyCAcceptorToLAcceptor(s: CAcceptor) : LAcceptor 
    requires CAcceptorIsAbstractable(s) { ... ... }
```
For the complete code, please refer to `Acceptor.i.dfy` in the RSL directory.

By default, AutoMan names the concrete implementation by either adding a C at the beginning or replacing the first character with C if the name starts with L:
```
LAcceptor -> CAcceptor
```

Users can customize renaming rules by writing them in a JSON file.
We have provided an example at `./asset/remapping.json`.

## Functionalization

The core translation performed by AutoMan is to convert a specification written in Dafny TLA into a functional system implementation, also in the Dafny language.
AutoMan supports commonly used TLA syntax:
1. Let-Binding.
2. Sub-statements connected by the `&&` operator.
3. `if-else` statement.
4. Call other actions.
5. Member check using the `==` symbol.
6. `forall` quantifier used to describe `maps` and `sequences`.
7. Data update, collection member access, helper function calls, operators, etc., applied within the core expressions mentioned above.

Here's an example of translation:
```
predicate LAcceptorTruncateLog(s:LAcceptor, s':LAcceptor, opn:OperationNumber)
{
if opn <= s.log_truncation_point then
    s' == s
else
    && RemoveVotesBeforeLogTruncationPoint(s.votes, s'.votes, opn)
    && s' == s.(log_truncation_point := opn, votes := s'.votes)
}
```
->
```
function method CAcceptorTruncateLog(s: CAcceptor, opn: COperationNumber) : CAcceptor 
    requires CAcceptorIsValid(s)
    requires COperationNumberIsValid(opn)
    ensures var s' := CAcceptorTruncateLog(s, opn); CAcceptorIsValid(s') && LAcceptorTruncateLog(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
{
    var t1 := 
        if opn <= s.log_truncation_point then 
            var t1 := 
                s; 				
            t1 
        else 
            var t1 := 
                CRemoveVotesBeforeLogTruncationPoint(s.votes, opn); 				
            var t2 := 
                s.(log_truncation_point := opn, votes := t1); 				
            t2; 		
    t1
}
```
To define the scope of translation and ensure accurate translation, AutoMan imposes certain requirements on the specification's writing, which must pass AutoMan's checks before translation can proceed.

For specifications that do not pass the checks, AutoMan will print the errors as comments in the generated code.
Please refer to `./asset/BadExamples` to find specific examples.

Next, we will introduce the writing guidelines that users need to follow and the corresponding checks implemented by AutoMan.

## Annotation for input and output

The signature of a specification will be split into inputs and outputs in the implementation. 
AutoMan requires users to provide annotations for this.

The annotation `AcceptorTruncateLog(+, -, +);` 
indicates that the first and third parameters are in input mode, while the second parameter is in output mode.
The translation of the signature will proceed as follows::
```
predicate LAcceptorTruncateLog(s:LAcceptor, s':LAcceptor, opn:OperationNumber)
```
->
```
function method CAcceptorTruncateLog(s: CAcceptor, opn: COperationNumber) : CAcceptor
```
.

## Assignment of a member

The assignment of a member can be done by 
1. A member appears alone on one side of the `==` expression.
```
&& a.max_bal == Ballot(0,0)
->
var t2 := CBallot(0, 0); 	
CAcceptor(..., t2, ...)	
```
2. Calls another action to assign a value to the member.
```
&& ElectionStateReflectReceivedRequest(s.election_state, s'.election_state, val)
->
var t1 := CElectionStateReflectReceivedRequest(s.election_state, val); 
```
3. Through universal quantifiers for collections, which is explained below.

## Saturation check

Based on the mode annotations provided by users, AutoMan checks whether each parameter labeled as output is fully assigned.
AutoMan will construct a symbol table to recursively obtain the structure of the DataType and analyze whether each member is fully assigned.

In this example, the member assignment for `constants` in `a:LAcceptor` is incomplete:

```
predicate LAcceptorInit(a:LAcceptor, c:LReplicaConstants)
{
    // && a.constants == c
    && a.max_bal == Ballot(0,0)
    && a.votes == map []
    && |a.last_checkpointed_operation| == |c.all.config.replica_ids|
    && (forall idx :: 0 <= idx < |a.last_checkpointed_operation| ==> a.last_checkpointed_operation[idx] == 0)
    && a.log_truncation_point == 0
}
```
and therefore will fail AutoMan's saturation check:
```
[Action] LAcceptorInit
Saturation check failed: Output-mode variables are not fully assigned
```
.

## Then-branch and else-branch must assign the same set of variables

AutoMan requires that the branches of an if-else expression check the values of the same set of members.

In this example
```
if 0 <= sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then
    s'.last_checkpointed_operation == s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt]
    && s'.constants == s.constants
    && s'.max_bal == s.max_bal
    // && s'.votes == s.votes
    && s'.log_truncation_point == s.log_truncation_point
else
    s' == s
```
the `else` branch assigns the entire value of `s'`, while the `if` branch misses one member, which will trigger a check failure:
```
[Action] LAcceptorProcessHeartbeat
Then-branch and else-branch do not assign the same set of variables: 
	if 0 <= sender_index && sender_index < |s.last_checkpoi ... ... 
```
.

## Harmony check

AutoMan requires that each member be assigned a value only once.

In this example
```
&& s'.constants == s.constants
&& s'.constants == 10
```
the assignment for sub-member `constants` is conducted twice, which will trigger a check failure:
```
[Action] LAcceptorProcess2a
Harmony check failed: 
	This output-mode variable has been assigned multiple times: 
		s'.constants
```
.

## Obligation check 

AutoMan requires that a value marked as output must assign values to other variables only after it has been assigned itself.

In the current checks, AutoMan verifies whether a member has been assigned based on the order of code execution.

In this example:
```
if opn <= s.log_truncation_point then
    s' == s
else
    // && RemoveVotesBeforeLogTruncationPoint(s.votes, s'.votes, opn)
    && s' == s.(log_truncation_point := opn, votes := s'.votes)
```
`s'.votes` is used in the data update expression without being assigned, which will trigger a check failure:

```
[Action] LAcceptorTruncateLog
This expr contains an output-mode variable that is 
	not assigned in the previous context:
	s.(log_truncation_point := opn, votes := s'.votes)
```
.

## Universal quantifiers for collections

For the `forall` quantifier used to describe collections, AutoMan requires the specification to be written in strict accordance with the provided template.

An Example:
```
&& (forall opn :: opn in votes' <==> opn in votes && opn >= log_truncation_point)
&& (forall opn :: opn in votes' ==> votes'[opn] == votes[opn])
```
->
```
var t1 := 
    (map opn | opn in votes && opn >= log_truncation_point :: votes[opn]); 		
t1
```
.

The details about the templates and the motivation behind it can be found at
`./doc/universal-quantification-templates.md`.
Failure to follow the templates may result in undetected assignments to collections.


