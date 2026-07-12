---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,                   \* set of node identifiers
    SlushLoopProcess,       \* set of loop process identifiers (one per node)
    SlushQueryProcess,      \* set of query process identifiers (one per node)
    HostMapping,            \* function from loop processes to query processes
    SlushIterationCount,    \* number of iterations each loop process must perform
    SampleSetSize,          \* size of each query sample
    PickFlipThreshold,      \* number of matching replies required to flip color
    NoColor,                \* special value meaning “uncolored”
    NoMessage               \* special value meaning “no message”

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
LoopSet == SlushLoopProcess
QuerySet == SlushQueryProcess

\* ----------------------------------------------------------------------
\* Basic types
\* ----------------------------------------------------------------------
Color == {"Red", "Blue"} \* the two possible colors
MsgKind == {"Query", "Reply", "Terminate"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,      \* [node -> Color \/ NoColor]
    msgSet,      \* set of messages (tuples)
    pc,          \* program counter function: [process -> {"Init","WaitColor","Sample","Reply","Tally","Done","ClientReq","ClientDone"}]
    sampleSet,   \* [loopProc -> SUBSET Node]  -- peers sampled in current round
    iteration    \* [loopProc -> Nat]         -- number of completed iterations

\* ----------------------------------------------------------------------
\* Message definitions
\* ----------------------------------------------------------------------
QueryMsg == [kind |-> "Query", sender |-> SlushLoopProcess, receiver |-> SlushQueryProcess, color |-> Color]
ReplyMsg == [kind |-> "Reply", sender |-> SlushQueryProcess, receiver |-> SlushLoopProcess, color |-> Color]
TerminateMsg == [kind |-> "Terminate", sender |-> SlushLoopProcess, receiver |-> SlushQueryProcess]

Msg == QueryMsg \cup ReplyMsg \cup TerminateMsg

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgSet = {}
    /\ pc = [p \in LoopSet \cup QuerySet |-> "Init"]
    /\ sampleSet = [p \in LoopSet |-> {}]
    /\ iteration = [p \in LoopSet |-> 0]
    /\ pc[SlushLoopProcess] = "WaitColor"   \* loop processes start waiting for color
    /\ pc[SlushQueryProcess] = "ReplyLoop"  \* query processes start in reply loop
    /\ pc[ClientReq] = "AssignColor"        \* client process (identified below)

\* ----------------------------------------------------------------------
\* Helper: next sample set (random selection; nondeterministic choice)
\* ----------------------------------------------------------------------
NextSample(p) ==
    /\ p \in LoopSet
    /\ \E s \in Subset(Node \ {p}) :
          /\ Cardinality(s) = SampleSetSize
          /\ sampleSet' = [sampleSet EXCEPT ![p] = s]
          /\ UNCHANGED << colors, msgSet, pc, iteration >>

\* ----------------------------------------------------------------------
\* Query message sending by loop process
\* ----------------------------------------------------------------------
SendQuery(p) ==
    /\ p \in LoopSet
    /\ pc[p] = "Sample"
    /\ \E m \in Msg :
          /\ m.kind = "Query"
          /\ m.sender = p
          /\ m.receiver \in HostMapping[p]
          /\ m.color = colors[HostMapping[p][1]]   \* color of host node (simplified)
          /\ msgSet' = msgSet \cup {m}
          /\ pc' = [pc EXCEPT ![p] = "Reply"]
          /\ UNCHANGED << colors, sampleSet, iteration >>

\* ----------------------------------------------------------------------
\* Query process replies to query messages (and adopts color if uncolored)
\* ----------------------------------------------------------------------
ReplyToQuery(q) ==
    /\ q \in QuerySet
    /\ \E m \in msgSet :
          /\ m.kind = "Query"
          /\ m.receiver = q
          /\ \E reply \in Msg :
                /\ reply.kind = "Reply"
                /\ reply.sender = q
                /\ reply.receiver = m.sender
                /\ reply.color = IF colors[HostMapping[q][1]] = NoColor
                                 THEN m.color
                                 ELSE colors[HostMapping[q][1]]
          /\ msgSet' = (msgSet \ {m}) \cup {reply}
          /\ colors' = IF colors[HostMapping[q][1]] = NoColor
                       THEN [colors EXCEPT ![HostMapping[q][1]] = reply.color]
                       ELSE colors
          /\ pc' = [pc EXCEPT ![q] = "ReplyLoop"]
          /\ UNCHANGED << sampleSet, iteration >>

\* ----------------------------------------------------------------------
\* Loop process tallies replies and possibly flips color
\* ----------------------------------------------------------------------
TallyAndMaybeFlip(p) ==
    /\ p \in LoopSet
    /\ pc[p] = "Reply"
    /\ msgsFromSample == { m \in msgSet : m.kind = "Reply" /\ m.receiver = p /\ m.sender \in HostMapping[p] }
    /\ Cardinality(msgsFromSample) = SampleSetSize
    /\ counts == [c \in Color |-> Cardinality({ m \in msgsFromSample : m.color = c })]
    /\ newColor == IF counts["Red"] >= PickFlipThreshold THEN "Red"
                  ELSE IF counts["Blue"] >= PickFlipThreshold THEN "Blue"
                  ELSE colors[HostMapping[p][1]]
    /\ colors' = [colors EXCEPT ![HostMapping[p][1]] = newColor]
    /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = IF iteration[p] + 1 = SlushIterationCount THEN "Done" ELSE "Sample"]
    /\ msgSet' = msgSet \ msgsFromSample
    /\ UNCHANGED << sampleSet, HostMapping, NoMessage >>

\* ----------------------------------------------------------------------
\* Loop process sends termination message after completing iterations
\* ----------------------------------------------------------------------
SendTerminate(p) ==
    /\ p \in LoopSet
    /\ pc[p] = "Done"
    /\ \E t \in Msg :
          /\ t.kind = "Terminate"
          /\ t.sender = p
          /\ t.receiver \in SlushQueryProcess
    /\ msgSet' = msgSet \cup {t}
    /\ pc' = [pc EXCEPT ![p] = "Terminated"]
    /\ UNCHANGED << colors, sampleSet, iteration >>

\* ----------------------------------------------------------------------
\* Client assigns color to an uncolored node
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ pc[ClientReq] = "AssignColor"
    /\ \E n \in Node :
          /\ colors[n] = NoColor
          /\ \E c \in Color :
                /\ colors' = [colors EXCEPT ![n] = c]
                /\ pc' = [pc EXCEPT ![ClientReq] = IF \E m \in msgSet : m.kind = "Terminate" /\ Cardinality(m) = Cardinality(LoopSet) THEN "ClientDone" ELSE "AssignColor"]
                /\ UNCHANGED << msgSet, sampleSet, iteration >>

\* ----------------------------------------------------------------------
\* Query loop exit when all loop processes terminated
\* ----------------------------------------------------------------------
QueryExit(q) ==
    /\ q \in QuerySet
    /\ pc[q] = "ReplyLoop"
    /\ \E tMsgs \in msgSet :
          /\ \A p \in LoopSet : tMsgs = { m \in msgSet : m.kind = "Terminate" /\ m.receiver = q }
    /\ pc' = [pc EXCEPT ![q] = "Exited"]
    /\ UNCHANGED << colors, msgSet, sampleSet, iteration >>

\* ----------------------------------------------------------------------
\* NEXT action (non-deterministic choice among enabled actions)
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in LoopSet : NextSample(p)
    \/ \E p \in LoopSet : SendQuery(p)
    \/ \E q \in QuerySet : ReplyToQuery(q)
    \/ \E p \in LoopSet : TallyAndMaybeFlip(p)
    \/ \E p \in LoopSet : SendTerminate(p)
    \/ \E q \in QuerySet : QueryExit(q)
    \/ ClientAssign

\* ----------------------------------------------------------------------
\* Safety invariant (type invariant)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> (Color \cup {NoColor})]
    /\ msgSet \subseteq Msg
    /\ pc \in [LoopSet \cup QuerySet \cup {ClientReq} -> {"Init","WaitColor","Sample","Reply","Tally","Done","Terminated","ReplyLoop","Exited","AssignColor","ClientDone"}]
    /\ sampleSet \in [LoopSet -> SUBSET Node]
    /\ iteration \in [LoopSet -> Nat]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgSet, pc, sampleSet, iteration>>

====