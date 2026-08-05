---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush is the simplest member of the Snow algorithm family (the Avalanche   *)
(* whitepaper).  Each node repeatedly samples a random subset of peers and   *)
(* adopts a strictly popular color; the network then metastably converges   *)
(* on a single color.  Because TLA+ has no probabilistic primitives, this     *)
(* spec is a deterministic template for the protocol's message flow.           *)

CONSTANTS
  Node,                     \* physical nodes in the network
  SlushLoopProcess,          \* per-node process driving the Slush loop
  SlushQueryProcess,         \* per-node process answering queries
  HostMapping,              \* triples linking a node to its loop and query processes
  SlushIterationCount,      \* max loop iterations per node
  SampleSetSize,            \* size of the peer sample each iteration
  PickFlipThreshold,        \* replies of one color needed to flip
  NoColor,                  \* sentinel for an uncolored node
  NoMessage                 \* sentinel for a non-existent message

\* A message is a tuple whose shape depends on its type (query, reply, or termination).
Message == Union(
  {<<SlushLoopProcess, "query", SlushQueryProcess, NoColor>>},
  {<<SlushQueryProcess, "reply", SlushLoopProcess, NoColor>>},
  {<<SlushLoopProcess, "done", NoMessage, NoMessage>>}
)

VARIABLES
  assignedColor,    \* [Node -> {NoColor, "red", "yellow"}] : node's current color
  messages,         \* in-flight messages
  pc,               \* [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> Nat] : step each process is on
  sampleSet,        \* [SlushLoopProcess -> SUBSET SlushQueryProcess] : sampled peers this round
  iterationCount    \* [SlushLoopProcess -> Nat] : loop iterations completed

vars == <<assignedColor, messages, pc, sampleSet, iterationCount>>

TypeInvariant ==
  /\ assignedColor \in [Node -> {NoColor, "red", "yellow"}]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> Nat]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterationCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ assignedColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> 0]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ iterationCount = [lp \in SlushLoopProcess |-> 0]

\* The client arbitrarily seeds an uncolored node with a random color.
ClientAssignsColor ==
  /\ pc["client"] = 0
  /\ \E n \in Node :
       /\ assignedColor[n] = NoColor
       /\ \E c \in {"red", "yellow"} : assignedColor' = [assignedColor EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sampleSet, iterationCount>>

RequireColor ==
  /\ \A lp \in SlushLoopProcess :
       \E n \in Node : pc[lp] = 0 /\ <<n, lp, _>> \in HostMapping /\ assignedColor[n] # NoColor
  /\ pc' = [lp \in SlushLoopProcess |-> 1]
  /\ UNCHANGED <<assignedColor, messages, sampleSet, iterationCount>>

\* The loop process samples a random peer subset and queries each sampled peer.
QuerySampleSet ==
  /\ \A lp \in SlushLoopProcess :
       pc[lp] = 1 /\ iterationCount[lp] < SlushIterationCount
       => \E Q \in SUBSET SlushQueryProcess :
            /\ Cardinality(Q) = SampleSetSize
            /\ Q # {}
            /\ sampleSet' = [sampleSet EXCEPT ![lp] = Q]
            /\ messages' = messages \cup {<<lp, "query", qp, NoColor>> : qp \in Q}
  /\ pc' = [lp \in SlushLoopProcess |-> 2]
  /\ UNCHANGED <<assignedColor, iterationCount>>

\* A query process answers by replying with its own color; if uncolored, it adopts
\* the incoming query's color before replying.
RespondToQuery ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = 0
       /\ \E m \in messages :
            /\ m[1] = lp \in SlushLoopProcess /\ m[3] = qp
            /\ LET n \in Node : <<n, lp, qp>> \in HostMapping IN
                 /\ assignedColor' = IF assignedColor[n] = NoColor
                                    THEN [assignedColor EXCEPT ![n] = m[4]]
                                    ELSE assignedColor
                 /\ messages' = (messages \ {m}) \cup {<<qp, "reply", lp, assignedColor[n]>>}
            /\ pc' = [pc EXCEPT ![qp] = 1]
            /\ UNCHANGED <<sampleSet, iterationCount>>
  /\ UNCHANGED assignedColor

\* The loop process tallies replies and flips only on strict majority.
TallyReplies ==
  /\ \A lp \in SlushLoopProcess :
       /\ pc[lp] = 2
       /\ Cardinality(sampleSet[lp]) > 0
       => \E c \in {"red", "yellow"} :
            /\ Cardinality({m \in messages : m[1] = qp \in sampleSet[lp] /\ m[3] = lp /\ m[4] = c}) >= PickFlipThreshold
            /\ assignedColor' = [n \in Node : <<n, lp, _>> \in HostMapping => assignedColor EXCEPT ![n] = c]
            /\ iterationCount' = [iterationCount EXCEPT ![lp] = iterationCount[lp] + 1]
            /\ messages' = {m \in messages : m[1] = qp \in sampleSet[lp] /\ m[3] = lp} \cup
                           {m \in messages : m[1] = lp} \cup {<<lp, "done", NoMessage, NoMessage>>}
            /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
            /\ pc' = [pc EXCEPT ![lp] = 1]
  /\ UNCHANGED assignedColor

LoopTermination ==
  /\ \A lp \in SlushLoopProcess : pc[lp] = 1 /\ iterationCount[lp] >= SlushIterationCount
  /\ messages' = messages \cup {<<lp, "done", NoMessage, NoMessage>> : lp \in SlushLoopProcess}
  /\ pc' = [pc EXCEPT ![lp \in SlushLoopProcess] = 3]
  /\ UNCHANGED <<assignedColor, sampleSet, iterationCount>>

QueryLoopExit ==
  /\ \A qp \in SlushQueryProcess : pc[qp] = 1 /\ pc' = [pc EXCEPT ![qp] = 2]
  /\ \A lp \in SlushLoopProcess : <<lp, "done", NoMessage, NoMessage>> \in messages
       => \A qp \in SlushQueryProcess : pc[qp] = 2
  /\ UNCHANGED <<assignedColor, messages, sampleSet, iterationCount>>

Next ==
  \/ ClientAssignsColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)
        /\ WF_vars(QueryLoopExit)

AllProcessesEventuallyDone == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = 3)

====