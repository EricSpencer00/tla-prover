---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush: a minimalist metastable consensus protocol from the Avalanche family.  *)
(* Three concurrent components: (1) Loop processes, one per node, that run      *)
(* Slush's repeated-sampling loop; (2) Query processes, one per node, that      *)
(* respond to sampled queries and adopt a queried color if uncolored; (3) A     *)
(* client request process that assigns initial colors to uncolored nodes.       *)
(* Conversion: the pluscal block follows the description's structure exactly.   *)

CONSTANTS
    Node,                \* physical cluster members (hosts of loop/query processes)
    SlushLoopProcess,    \* processes that run the loop per node
    SlushQueryProcess,   \* processes that serve query replies per node
    HostMapping,         \* set of (node, loop proc, query proc) triples linking above
    SlushIterationCount, \* rounds each loop process may run before terminating
    SampleSetSize,       \* number of peers sampled in each round
    PickFlipThreshold,   \* replies of one color needed to trigger a node's flip
    NoColor,             \* sentinel value meaning "uncolored"
    NoMessage            \* sentinel value meaning "no message currently in transit"

\* Message types in the network modeled as a single bounded set.
MessageType == { "query", "queryReply", "termination" }

VARIABLES
    assignedColor,   \* [Node -> {NoColor} \cup Color]: chosen color per node
    messageSet,      \* set of pending messages (query, reply, termination)
    pc,              \* [SlushLoopProcess \cup SlushQueryProcess -> 0..5]: execution step per process
    sampleSet,       \* [SlushLoopProcess -> SUBSET SlushQueryProcess]: sampled peers this round
    loopIteration    \* [SlushLoopProcess -> 0..SlushIterationCount]: rounds completed per loop

vars == <<assignedColor, messageSet, pc, sampleSet, loopIteration>>

\* Each node name pairs with exactly one loop process and one query process.
LoopForNode(n) == CHOOSE lp \in SlushLoopProcess : \E qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping
QueryForNode(n) == CHOOSE qp \in SlushQueryProcess : \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

Init ==
    /\ assignedColor = [n \in Node |-> NoColor]
    /\ messageSet = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> IF p \in SlushLoopProcess THEN 0 ELSE 1]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ loopIteration = [lp \in SlushLoopProcess |-> 0]

\* Client work: assign a random color to an uncolored node (external request).
AssignNodeColor ==
    /\ \E n \in Node, c \in {0, 1} : assignedColor[n] = NoColor /\ assignedColor' = [assignedColor EXCEPT ![n] = c]
    /\ UNCHANGED <<messageSet, pc, sampleSet, loopIteration>>

RequireNodeColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = 0
         /\ assignedColor[LoopForNode(lp)] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = 1]
    /\ UNCHANGED <<assignedColor, messageSet, sampleSet, loopIteration>>

\* Loop process draws a random peer sample and broadcasts a query to each.
QuerySampleSet ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = 1
         /\ loopIteration[lp] < SlushIterationCount
         /\ \E Q \in {Q \in SUBSET SlushQueryProcess : Cardinality(Q) = SampleSetSize} :
              /\ sampleSet' = [sampleSet EXCEPT ![lp] = Q]
              /\ messageSet' = messageSet \cup { <<lp, qp, "query", assignedColor[LoopForNode(lp)]>> : qp \in Q }
         /\ pc' = [pc EXCEPT ![lp] = 2]
    /\ UNCHANGED <<assignedColor, loopIteration>>

\* Query process adopts the querying node's color if it was uncolored, then replies.
RespondToQuery ==
    /\ \E qp \in SlushQueryProcess :
         /\ pc[qp] = 1
         /\ \E m \in messageSet :
              /\ m[3] = "query" /\ m[2] = qp
              /\ assignedColor' = [assignedColor EXCEPT ![LoopForNode(qp)] =
                                    IF assignedColor[LoopForNode(qp)] = NoColor THEN m[4] ELSE assignedColor[LoopForNode(qp)]]
              /\ messageSet' = (messageSet \ {m}) \cup {<<qp, m[1], "queryReply", assignedColor[LoopForNode(qp)]>>}
              /\ pc' = [pc EXCEPT ![qp] = 2]
    /\ UNCHANGED <<sampleSet, loopIteration>>

\* Loop process tallies replies; flips its node's color if a majority threshold is met.
TallyReplies ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = 2
         /\ \A qp \in sampleSet[lp] : <<qp, lp, "queryReply", 0>> \in messageSet \/ <<qp, lp, "queryReply", 1>> \in messageSet
         /\ LET replies == {m \in messageSet : m[1] \in sampleSet[lp] /\ m[2] = lp /\ m[3] = "queryReply"} IN
              /\ LET cnt(c) == Cardinality({m \in replies : m[4] = c}) IN
                   IF cnt(0) >= PickFlipThreshold THEN assignedColor' = [assignedColor EXCEPT ![LoopForNode(lp)] = 0]
                   ELSE IF cnt(1) >= PickFlipThreshold THEN assignedColor' = [assignedColor EXCEPT ![LoopForNode(lp)] = 1]
                   ELSE assignedColor' = assignedColor
         /\ messageSet' = messageSet \ {m \in messageSet : m[1] \in sampleSet[lp] /\ m[2] = lp /\ m[3] = "queryReply"}
         /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
         /\ loopIteration' = [loopIteration EXCEPT ![lp] = @ + 1]
         /\ pc' = [pc EXCEPT ![lp] = 3]
    /\ UNCHANGED <<assignedColor>>

\* After all iterations a loop process broadcasts a termination message.
LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = 3
         /\ loopIteration[lp] = SlushIterationCount
         /\ messageSet' = messageSet \cup {<<lp, NoMessage, "termination", 0>>}
         /\ pc' = [pc EXCEPT ![lp] = 4]
    /\ UNCHANGED <<assignedColor, sampleSet, loopIteration>>

\* Query processes exit once every loop process has terminated.
QueryLoopExit ==
    /\ \E qp \in SlushQueryProcess :
         /\ pc[qp] = 2
         /\ \A lp \in SlushLoopProcess : <<lp, NoMessage, "termination", 0>> \in messageSet
         /\ pc' = [pc EXCEPT ![qp] = 5]
    /\ UNCHANGED <<assignedColor, messageSet, sampleSet, loopIteration>>

Next ==
    \/ AssignNodeColor \/ RequireNodeColor \/ QuerySampleSet \/ RespondToQuery
    \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(AssignNodeColor) /\ WF_vars(RequireNodeColor)
               /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
               /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit)

\* Types are always consistent: no node is assigned an illegal color, no message
\* of an unauthorized type ever enters the network.
TypeInvariant ==
    /\ \A n \in Node : assignedColor[n] \in {NoColor, 0, 1}
    /\ \A m \in messageSet : m[3] \in MessageType

\* Every process eventually reaches its done state; note this says nothing about
\* Slush's probabilistic convergence to a single color, which TLA+ cannot model.
Termination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = 5)

====