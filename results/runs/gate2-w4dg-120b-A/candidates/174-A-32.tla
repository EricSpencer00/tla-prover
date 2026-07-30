---- MODULE Slush ----
EXTENDS Naturals, Sequences

CONSTANTS
    Node
    SlushLoopProcess
    SlushQueryProcess
    HostMapping
    SlushIterationCount
    SampleSetSize
    PickFlipThreshold
    NoColor
    NoMessage

\* SlushLoopProcess iterates the main protocol loop; SlushQueryProcess replies to
\* query messages on behalf of its host node (adopting the query's color if
\* uncolored); HostMapping ties each process to its host node. Messages are
\* modelled as an unordered set of typed payloads; SampleSet tracks which peers
\* the current round has queried, and IterCount counts completed rounds.
VARIABLES
    Color
    Messages
    LoopPc
    QueryPc
    SampleSet
    IterCount

vars == <<Color, Messages, LoopPc, QueryPc, SampleSet, IterCount>>

\* Message types: a Slush query, a query reply, and a termination notice.
MessageTypes == {"SlushQuery", "SlushQueryReply", "SlushLoopTerminate"}
Colors == {"pickRed", "pickBlue"}

Message == [kind: MessageTypes, from: SlushLoopProcess, to: SlushQueryProcess, subject: Colors \cup {NoColor}]
QueryReply == [kind: "SlushQueryReply", from: SlushQueryProcess, to: SlushLoopProcess, subject: Colors \cup {NoColor}]
Termination == [kind: "SlushLoopTerminate", from: SlushLoopProcess, to: SlushLoopProcess, subject: NoMessage]
\* SlushQuery and SlushQueryReply share the same Message schema; SlushLoopTerminate
\* is a separate schema, so the message set has a homogeneous record type.
MessageUnion == Message \cup QueryReply \cup Termination

\* Loop and query processes are paired with their host node by HostMapping.
NodeOf(lp, qp) == \E n \in Node : <<n, lp, qp>> \in HostMapping

\* A loop process samples a random subset of distinct peer query processes.
RandomSample(lp, qp) == NodeOf(lp, qp) /\ Cardinality(SampleSet[lp]) < SampleSetSize

\* A reply is routed back to the originating loop process.
ReplyTo(lp, qp) == NodeOf(lp, qp) /\ \E b \in Color : [kind |-> "SlushQueryReply", from |-> qp, to |-> lp, subject |-> b] \in Messages

Init ==
    /\ Color = [n \in Node |-> NoColor]
    /\ Messages = {}
    /\ LoopPc = [lp \in SlushLoopProcess |-> "WaitForColor"]
    /\ QueryPc = [qp \in SlushQueryProcess |-> "ReplyLoop"]
    /\ SampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ IterCount = [lp \in SlushLoopProcess |-> 0]

\* The client process assigns a color to an uncolored node (the only external
\* event in this protocol, so it has its own action).
ClientAssignColor(n, c) ==
    /\ Color[n] = NoColor
    /\ Color' = [Color EXCEPT ![n] = c]
    /\ UNCHANGED <<Messages, LoopPc, QueryPc, SampleSet, IterCount>>

RequireColor(lp) ==
    /\ LoopPc[lp] = "WaitForColor"
    /\ \E n \in Node : NodeOf(lp, n) /\ Color[n] # NoColor
    /\ LoopPc' = [LoopPc EXCEPT ![lp] = "Query"]
    /\ UNCHANGED <<Color, Messages, QueryPc, SampleSet, IterCount>>

\* The sampling step fixes the loop process's current color as the subject of
\* every query it emits in this round (so replies reflect the sampling state).
QuerySampleSet(lp, qp) ==
    /\ LoopPc[lp] = "Query"
    /\ RandomSample(lp, qp)
    /\ \E c \in Colors : [kind |-> "SlushQuery", from |-> lp, to |-> qp, subject |-> c] \in Messages
    /\ SampleSet' = [SampleSet EXCEPT ![lp] = SampleSet[lp] \cup {qp}]
    /\ UNCHANGED <<Color, Messages, LoopPc, QueryPc, IterCount>>

\* A query process adopts its query's color when it is uncolored, then replies
\* with the (now) current color.
RespondToQuery(lp, qp) ==
    /\ \E m \in Messages : m.kind = "SlushQuery" /\ m.from = lp /\ m.to = qp
    /\ ~ReplyTo(lp, qp)
    /\ Color' = IF Color[NodeOf(lp, qp)] = NoColor THEN [Color EXCEPT ![NodeOf(lp, qp)] = m.subject] ELSE Color
    /\ Messages' = {[kind |-> "SlushQueryReply", from |-> qp, to |-> lp, subject |-> Color[NodeOf(lp, qp)]]} \cup (\{m \in Messages : m.from # lp \/ m.kind # "SlushQuery"})

\* Tallying waits for the full sample; a strict majority is not required here --
\* the flip threshold is a fixed constant, so a two-color tie may flip nothing.
TallyReplies(lp) ==
    /\ LoopPc[lp] = "Query"
    /\ Cardinality(SampleSet[lp]) = SampleSetSize
    /\ \A qp \in SampleSet[lp] : ReplyTo(lp, qp)
    /\ \E c \in Colors :
         LET Count == Cardinality({m \in Messages : m.kind = "SlushQueryReply" /\ m.to = lp /\ m.subject = c})
         IN IF Count >= PickFlipThreshold
            THEN Color' = [Color EXCEPT ![NodeOf(lp, lp)] = c]
            ELSE Color' = Color
    /\ SampleSet' = [SampleSet EXCEPT ![lp] = {}]
    /\ LoopPc' = IF IterCount[lp] < SlushIterationCount THEN "Query" ELSE "Terminate"
    /\ IterCount' = [IterCount EXCEPT ![lp] = IF IterCount[lp] < SlushIterationCount THEN IterCount[lp] + 1 ELSE @]
    /\ UNCHANGED QueryPc

LoopTermination(lp) ==
    /\ LoopPc[lp] = "Terminate"
    /\ LoopPc' = [LoopPc EXCEPT ![lp] = "TerminateSent"]
    /\ Messages' = {[kind |-> "SlushLoopTerminate", from |-> lp, to |-> lp, subject |-> NoMessage]} \cup (\{m \in Messages : m.kind # "SlushQuery"})
    /\ UNCHANGED <<Color, QueryPc, SampleSet, IterCount>>

QueryLoopExit(qp) ==
    /\ QueryPc[qp] # "Done"
    /\ \A lp \in SlushLoopProcess : [kind |-> "SlushLoopTerminate", from |-> lp, to |-> lp, subject |-> NoMessage] \in Messages
    /\ QueryPc' = [QueryPc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<Color, Messages, LoopPc, SampleSet, IterCount>>

Next ==
    \/ \E n \in Node, c \in Colors : ClientAssignColor(n, c)
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess, qp \in SlushQueryProcess : QuerySampleSet(lp, qp)
    \/ \E lp \in SlushLoopProcess, qp \in SlushQueryProcess : RespondToQuery(lp, qp)
    \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
    \/ \E lp \in SlushLoopProcess : LoopTermination(lp)
    \/ \E qp \in SlushQueryProcess : QueryLoopExit(qp)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ Color \in [Node -> Colors \cup {NoColor}]
    /\ Messages \subseteq MessageUnion
    /\ LoopPc \in [SlushLoopProcess -> {"WaitForColor", "Query", "Terminate", "TerminateSent"}]
    /\ QueryPc \in [SlushQueryProcess -> {"ReplyLoop", "Done"}]
    /\ SampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ IterCount \in [SlushLoopProcess -> 0..SlushIterationCount]

\* Every process reaching a done state is the only liveness guarantee here;
\* convergence to a single color is a probabilistic guarantee the spec cannot
\* express, so no convergence property is checked.
Termination == <>(\A lp \in SlushLoopProcess : LoopPc[lp] = "TerminateSent")
              /\ <>(\A qp \in SlushQueryProcess : QueryPc[qp] = "Done")

====