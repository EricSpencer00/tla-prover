---- MODULE Slush ----
(* Slush: the simplest Snow-family probabilistic consensus protocol, modeled as
   executable PlusCal. Each node has a loop process that samples peers and adopts
   a majority color, and a query process that answers color queries. The spec
   tracks color assignments, in-flight messages, sample sets, and an iteration
   counter per loop process. PlusCal is used for the actions; TLA+ checks a
   type invariant and universal termination. *)

EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,               \* set of nodes in the network
  SlushLoopProcess,   \* set of loop processes (one per node)
  SlushQueryProcess,  \* set of query processes (one per node)
  HostMapping,        \* set of <<node, loopProc, queryProc>> linking a node to its two processes
  SlushIterationCount, \* max number of loop iterations per loop process
  SampleSetSize,      \* fixed size of the peer sample
  PickFlipThreshold,  \* count threshold that triggers a color flip
  NoColor,            \* sentinel for "uncolored" nodes
  NoMessage           \* sentinel for "no message"

\* A loop or query process hosts exactly one node; the mapping is functional in both
\* directions. Derive the round number of loop processes and the owning node of query processes.
SlushLoopStep == [p \in SlushLoopProcess |-> 0..SlushIterationCount]
SlushQueryStep == [q \in SlushQueryProcess |-> {"reply", "done"}]
SlushNode == [p \in SlushLoopProcess |-> CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping]

VARIABLES
  color,         \* Node -> {NoColor, "red", "blue"} : the node's current opinion
  message,       \* set of in-flight messages (queries, replies, termination notes)
  slushStep,     \* SlushLoopProcess -> 0..SlushIterationCount : loop iteration counter
  slushSample,   \* SlushLoopProcess -> SUBSET SlushQueryProcess : current round's sample
  slushLoopStep  \* SlushLoopProcess -> 0..SlushIterationCount : progress indicator

vars == <<color, message, slushStep, slushSample, slushLoopStep>>

\* The message set is a union of three disjoint shapes, each carrying the same
\* sender field (the loop process) plus other fields relevant to its shape.
Message == [Kind: {"query", "reply", "terminate"}, SlushLoop: SlushLoopProcess,
            SlushQuery: SlushQueryProcess, Tally: {"red", "blue", NoColor}]

TypeOK ==
  /\ color \in [Node -> {"red", "blue", NoColor}]
  /\ message \subseteq Message
  /\ slushStep \in [SlushLoopProcess -> 0..SlushIterationCount]
  /\ slushSample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ slushLoopStep \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ message = {}
  /\ slushStep = [p \in SlushLoopProcess |-> 0]
  /\ slushSample = [p \in SlushLoopProcess |-> {}]
  /\ slushLoopStep = [p \in SlushLoopProcess |-> 0]

\* The client process assigns an initial color to an uncolored node.
ClientAssignColor ==
  /\ \E n \in Node, c \in {"red", "blue"} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<message, slushStep, slushSample, slushLoopStep>>

\* A loop process cannot begin until its host node has been assigned a color.
RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ slushStep[p] = 0
       /\ color[SlushNode[p]] # NoColor
       /\ slushStep' = [slushStep EXCEPT ![p] = 1]
  /\ UNCHANGED <<color, message, slushSample, slushLoopStep>>

\* The loop process samples a random set of peers and sends each a query.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ slushStep[p] = 1
       /\ slushSample[p] = {}
       /\ Cardinality(SlushQueryProcess) >= SampleSetSize
       /\ \E sample \in SUBSET SlushQueryProcess :
            /\ Cardinality(sample) = SampleSetSize
            /\ slushSample' = [slushSample EXCEPT ![p] = sample]
            /\ message' = message \cup
                 { [Kind |-> "query", SlushLoop |-> p, SlushQuery |-> q, Tally |-> color[SlushNode[p]]]
                     : q \in sample }
  /\ slushStep' = [slushStep EXCEPT ![p] = 2]
  /\ UNCHANGED <<color, slushLoopStep>>

\* A query process adopts the sender's color if it is uncolored, then replies.
RespondToQuery ==
  /\ \E m \in message :
       /\ m.Kind = "query"
       /\ color' = [color EXCEPT ![SlushNode[m.SlushQuery]] =
                      IF color[SlushNode[m.SlushQuery]] = NoColor THEN m.Tally
                      ELSE color[SlushNode[m.SlushQuery]]]
       /\ message' = (message \ {m}) \cup
            {[Kind |-> "reply", SlushLoop |-> m.SlushLoop, SlushQuery |-> m.SlushQuery,
              Tally |-> IF color[SlushNode[m.SlushQuery]] = NoColor THEN m.Tally
                         ELSE color[SlushNode[m.SlushQuery]]]}
  /\ UNCHANGED <<slushStep, slushSample, slushLoopStep>>

\* Once all sampled peers have replied, the loop process tallies and flips the
\* node's color if a strict majority threshold is reached.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ slushStep[p] = 2
       /\ \A q \in slushSample[p] : \E m \in message :
            /\ m.Kind = "reply" /\ m.SlushLoop = p /\ m.SlushQuery = q
       /\ Cardinality({q \in slushSample[p] : \E m \in message :
            m.Kind = "reply" /\ m.SlushLoop = p /\ m.SlushQuery = q /\ m.Tally = "red"}) >= PickFlipThreshold
            => color' = [color EXCEPT ![SlushNode[p]] = "red"]
       /\ Cardinality({q \in slushSample[p] : \E m \in message :
            m.Kind = "reply" /\ m.SlushLoop = p /\ m.SlushQuery = q /\ m.Tally = "blue"}) >= PickFlipThreshold
            => color' = [color EXCEPT ![SlushNode[p]] = "blue"]
       /\ slushSample' = [slushSample EXCEPT ![p] = {}]
       /\ slushStep' = [slushStep EXCEPT ![p] = (IF slushLoopStep[p] < SlushIterationCount
                                                   THEN 1 ELSE 3)]
       /\ slushLoopStep' = [slushLoopStep EXCEPT ![p] =
                               IF slushLoopStep[p] < SlushIterationCount
                               THEN slushLoopStep[p] + 1 ELSE slushLoopStep[p]]
  /\ UNCHANGED <<message>>

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ slushStep[p] = 3
       /\ message' = message \cup
            {[Kind |-> "terminate", SlushLoop |-> p, SlushQuery |-> NoMessage, Tally |-> NoColor]}
       /\ slushStep' = [slushStep EXCEPT ![p] = 4]
  /\ UNCHANGED <<color, slushSample, slushLoopStep>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ \A p \in SlushLoopProcess : <<p, q>> \notin HostMapping
       /\ \A m \in message : m.Kind # "query" \/ m.SlushQuery # q
       /\ message' = message \cup {[Kind |-> "terminate", SlushLoop |-> NoMessage,
                                    SlushQuery |-> q, Tally |-> NoColor]}
  /\ UNCHANGED <<color, slushStep, slushSample, slushLoopStep>>

Next ==
  \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor)
         /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
         /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess : <>(slushStep[p] = 4)

====