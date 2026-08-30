---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* The Slush protocol is the simplest Snow-family consensus protocol.       *)
(* Nodes run loop processes that sample peers' colors and adopt a popular  *)
(* one; query processes answer color queries.  TLA+ has no native            *)
(* probability, so this is exercised as deterministic pseudocode.           *)

CONSTANTS
    Node,              \* the network's nodes
    SlushLoopProcess,  \* the loop process belonging to each node
    SlushQueryProcess, \* the query process belonging to each node
    HostMapping,       \* { <<n, lp, qp>> : lp and qp run on node n } (bijection)
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold,
    NoColor,
    NoMessage

\* A message is directed from one process to another and carries an optional
\* attached color (queries only ever carry the sender's current color).
Message == [to: {SlushLoopProcess} \cup {SlushQueryProcess}, from: SlushLoopProcess \cup SlushQueryProcess, kind: {"query", "queryReply", "terminate"}, payload: {NoColor} \cup {"c1", "c2"}]

\* A process runs the Slush loop (querying and possibly flipping) or the
\* query-reply loop (answering incoming queries).  Both share a single
\* message set, which is how backpressure is modeled: a full set blocks.
\* A loop process may only start its next iteration once it has closed
\* out the message set for the previous one (its replies have all arrived).

VARIABLES
    color,         \* [Node -> {NoColor, "c1", "c2"}] the current color per node
    inbox,         \* Set of Message : all in-flight messages
    pc,            \* [SlushLoopProcess \cup SlushQueryProcess -> {"ready", "waiting", "done"}] where each process is
    sampleSet,     \* [SlushLoopProcess -> SUBSET SlushQueryProcess] peers queried this round
    loopCount      \* [SlushLoopProcess -> 0..SlushIterationCount] completed iterations

vars == <<color, inbox, pc, sampleSet, loopCount>>

TypeOK ==
    /\ color \in [Node -> {NoColor, "c1", "c2"}]
    /\ inbox \subseteq Message
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"ready", "waiting", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ inbox = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "ready"]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ loopCount = [lp \in SlushLoopProcess |-> 0]

\* The client hands an initial color to an uncolored node; this is the only
\* way a node's color is set without consulting peers.
ClientAssign ==
    \E n \in Node, c \in {"c1", "c2"} :
        /\ color[n] = NoColor
        /\ color' = [color EXCEPT ![n] = c]
        /\ UNCHANGED <<inbox, pc, sampleSet, loopCount>>

RequireColor ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "ready"
        /\ \E n \in Node : <<n, lp, CHOOSE qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping>> \in HostMapping
        /\ color[n] # NoColor
        /\ pc' = [pc EXCEPT ![lp] = "waiting"]
    /\ UNCHANGED <<color, inbox, sampleSet, loopCount>>

QuerySampleSet ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "waiting"
        /\ loopCount[lp] < SlushIterationCount
        /\ sampleSet[lp] = {}
        /\ sampleSet' = [sampleSet EXCEPT ![lp] = {CHOOSE qp \in SlushQueryProcess :
                                                    <<CHOOSE n \in Node : <<n, lp, qp>> \in HostMapping, lp, qp>> \in HostMapping}]
        /\ inbox' = inbox \cup {[to |-> qp, from |-> lp, kind |-> "query", payload |-> color[CHOOSE n \in Node : <<n, lp, qp>> \in HostMapping]] : qp \in sampleSet[lp]}
    /\ UNCHANGED <<color, pc, loopCount>>

RespondToQuery ==
    \E qp \in SlushQueryProcess :
        /\ \E m \in inbox :
            /\ m.to = qp
            /\ m.kind = "query"
            /\ LET n == CHOOSE n \in Node : <<n, CHOOSE lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping, qp>> \in HostMapping
               IN /\ color[n] = NoColor => color' = [color EXCEPT ![n] = m.payload]
                  /\ inbox' = (inbox \ {m}) \cup {[to |-> m.from, from |-> qp, kind |-> "queryReply", payload |-> color[n]]}
    /\ UNCHANGED <<pc, sampleSet, loopCount>>

TallyReplies ==
    \E lp \in SlushLoopProcess :
        /\ sampleSet[lp] # {}
        /\ \A qp \in sampleSet[lp] : \E m \in inbox : m.to = lp /\ m.from = qp /\ m.kind = "queryReply"
        /\ LET tally == [c \in {"c1", "c2"} |-> Cardinality({m \in inbox : m.to = lp /\ m.kind = "queryReply" /\ m.payload = c})]
               n == CHOOSE n \in Node : <<n, lp, CHOOSE qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping>> \in HostMapping
               oldc == color[n]
               newc == IF tally["c1"] >= PickFlipThreshold THEN "c1" ELSE IF tally["c2"] >= PickFlipThreshold THEN "c2" ELSE oldc
           IN /\ color' = [color EXCEPT ![n] = newc]
              /\ inbox' = {m \in inbox : m.from \notin sampleSet[lp]}
        /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
        /\ loopCount' = [loopCount EXCEPT ![lp] = @ + 1]
    /\ pc' = pc

LoopTermination ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "waiting"
        /\ loopCount[lp] = SlushIterationCount
        /\ pc' = [pc EXCEPT ![lp] = "done"]
        /\ inbox' = inbox \cup {[to |-> lp, from |-> lp, kind |-> "terminate", payload |-> NoColor]}
    /\ UNCHANGED <<color, sampleSet, loopCount>>

QueryLoopExit ==
    /\ \A qp \in SlushQueryProcess : pc[qp] = "ready"
    /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
    /\ pc' = [p \in SlushLoopProcess \cup SlushQueryProcess |-> IF pc[p] = "ready" THEN "done" ELSE pc[p]]
    /\ UNCHANGED <<color, inbox, sampleSet, loopCount>>

Next == ClientAssign \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done")
====