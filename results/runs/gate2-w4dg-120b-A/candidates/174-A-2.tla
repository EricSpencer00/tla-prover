---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,                \* the nodes participating in Slush
    SlushLoopProcess,    \* the per-node loop processes
    SlushQueryProcess,   \* the per-node query processes
    HostMapping,         \* linking each loop and query process to its node
    SlushIterationCount, \* how many rounds each loop process runs for
    SampleSetSize,       \* how many peers each loop process samples per round
    PickFlipThreshold,   \* the reply count needed to adopt a color
    NoColor,             \* sentinel meaning a node has not been colored yet
    NoMessage            \* sentinel meaning no message is in flight

\* Message forms: each carries the ids of sender and receiver, plus the sender's
\* current color (or NoMessage) as payload.
Query == [src: SlushLoopProcess, dst: SlushQueryProcess, payload: {NoMessage} \cup {NoColor}]
Reply == [src: SlushQueryProcess, dst: SlushLoopProcess, payload: {NoMessage} \cup {NoColor}]
Terminate == [src: SlushLoopProcess, dst: NoMessage, payload: NoMessage]
Msgs == Query \cup Reply \cup Terminate

\* The host mapping is a set of triples; helpers below turn it into a lookup.
LoopHostOf(lp) == CHOOSE n \in Node : <<lp, n>> \in HostMapping
QueryHostOf(qp) == CHOOSE n \in Node : <<qp, n>> \in HostMapping

VARIABLES
    assignment,    \* [Node -> {NoColor} \cup (2..3)]
    messages,      \* set of in-flight messages of type Msgs
    pc,            \* [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "sampling", "collecting", "done"}]
    sample,        \* [SlushLoopProcess -> SUBSET SlushQueryProcess]
    iterations     \* [SlushLoopProcess -> 0..SlushIterationCount]

vars == <<assignment, messages, pc, sample, iterations>>

TypeInvariant ==
    /\ assignment \in [Node -> {NoColor} \cup (2..3)]
    /\ messages \subseteq Msgs
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "sampling", "collecting", "done"}]

Init ==
    /\ assignment = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "idle"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iterations = [lp \in SlushLoopProcess |-> 0]

\* The client assigns a random color to an uncolored node.
ClientAssignColor ==
    /\ \E n \in Node, c \in (2..3) :
         /\ assignment[n] = NoColor
         /\ assignment' = [assignment EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sample, iterations>>

RequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "idle"
         /\ assignment[LoopHostOf(lp)] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = "sampling"]
    /\ UNCHANGED <<assignment, messages, sample, iterations>>

\* The loop process picks a random sample of peers and queries them.
QuerySampleSet ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "sampling"
         /\ iterations[lp] < SlushIterationCount
         /\ Cardinality(sample[lp]) < SampleSetSize
         /\ \E qp \in SlushQueryProcess :
              /\ qp \notin sample[lp]
              /\ sample' = [sample EXCEPT ![lp] = @ \cup {qp}]
              /\ messages' = messages \cup
                    {[src |-> lp, dst |-> qp, payload |-> assignment[LoopHostOf(lp)]]}
    /\ UNCHANGED <<assignment, pc, iterations>>

\* A query process copies the sender's color into itself if it is uncolored,
\* then replies back with its own current color.
RespondToQuery ==
    /\ \E m \in messages :
         /\ m \in Query
         /\ \E a \in {NoColor} \cup (2..3) :
              /\ assignment' = [assignment EXCEPT ![QueryHostOf(m.dst)] = IF @ = NoColor THEN m.payload ELSE @]
              /\ messages' = (messages \ {m}) \cup
                    {[src |-> m.dst, dst |-> m.src, payload |-> assignment[QueryHostOf(m.dst)]]}
    /\ UNCHANGED <<pc, sample, iterations>>

\* The loop process waits for every sampled peer to reply, then adopts the
\* majority color only if it meets the flip threshold.
TallyReplies ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "collecting"
         /\ \A qp \in sample[lp] : \E m \in messages : m \in Reply /\ m.src = qp /\ m.dst = lp
         /\ \E c \in (2..3) :
              /\ Cardinality({ qp \in sample[lp] :
                    \E m \in messages : m \in Reply /\ m.src = qp /\ m.dst = lp /\ m.payload = c }) >= PickFlipThreshold
              /\ assignment' = [assignment EXCEPT ![LoopHostOf(lp)] = c]
         /\ sample' = [sample EXCEPT ![lp] = {}]
         /\ iterations' = [iterations EXCEPT ![lp] = @ + 1]
         /\ pc' = [pc EXCEPT ![lp] = "sampling"]
         /\ messages' = { m \in messages : ~(m \in Reply /\ m.dst = lp) }
    /\ UNCHANGED <<>>

LoopTermination ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "sampling"
         /\ iterations[lp] = SlushIterationCount
         /\ pc' = [pc EXCEPT ![lp] = "done"]
         /\ messages' = messages \cup {[src |-> lp, dst |-> NoMessage, payload |-> NoMessage]}
    /\ UNCHANGED <<assignment, sample, iterations>>

QueryLoopExit ==
    /\ \E qp \in SlushQueryProcess :
         /\ pc[qp] = "idle"
         /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
         /\ pc' = [pc EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<assignment, messages, sample, iterations>>

Next ==
    \/ ClientAssignColor
    \/ RequireColor
    \/ QuerySampleSet
    \/ RespondToQuery
    \/ TallyReplies
    \/ LoopTermination
    \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssignColor)
        /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet)
        /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies)
        /\ WF_vars(LoopTermination)
        /\ WF_vars(QueryLoopExit)

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[p] = "done")

====