---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(* Constants (to be instantiated in the .cfg file)                         *)
(***************************************************************************)
CONSTANTS
    Node,               \* The set of node identifiers
    SlushLoopProcess,   \* The set of loop process identifiers (one per node)
    SlushQueryProcess,  \* The set of query process identifiers (one per node)
    HostMapping,        \* The set of triples <<proc, "loop"|"query", node>>
    SlushIterationCount,\* Number of iterations each loop process performs
    SampleSetSize,      \* Number of peers sampled each round
    PickFlipThreshold,  \* Threshold of replies needed to flip color
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value meaning "no pending message"

(***************************************************************************)
(* Derived sets                                                          *)
(***************************************************************************)
Colors == {"Red", "Blue", NoColor}

MessageTypes == {"Query", "Reply", "Terminate"}

Msg == [type : {"Query", "Reply", "Terminate"},
        src  : (SlushLoopProcess \cup SlushQueryProcess),
        dst  : (SlushLoopProcess \cup SlushQueryProcess),
        color: Colors,
        loop : SlushLoopProcess \cup {NoMessage}]

(***************************************************************************)
(* Variables                                                             *)
(***************************************************************************)
VARIABLES
    colors,          \* [node -> color]
    msgs,            \* Set of in‑flight messages
    pc,              \* Program counter: [process -> Nat]
    sampleSet,       \* [loopProc -> SUBSET Node]
    iterCount        \* [loopProc -> Nat]

(***************************************************************************)
(* Helper definitions                                                    *)
(***************************************************************************)
\* Mapping from a node to its loop and query processes
LoopOf(node) == CHOOSE lp \in SlushLoopProcess : <<lp, "loop", node>> \in HostMapping
QueryOf(node) == CHOOSE qp \in SlushQueryProcess : <<qp, "query", node>> \in HostMapping

\* The set of all processes
AllProcs == SlushLoopProcess \cup SlushQueryProcess

\* Initial values
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in AllProcs |-> 0]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]

(***************************************************************************)
(* Actions                                                               *)
(***************************************************************************)

\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ \E n \in Node :
          /\ colors[n] = NoColor
          /\ \E col \in {"Red", "Blue"} :
                /\ colors' = [colors EXCEPT ![n] = col]
                /\ pc' = pc
                /\ msgs' = msgs
                /\ sampleSet' = sampleSet
                /\ iterCount' = iterCount
    /\ UNCHANGED <<pc, msgs, sampleSet, iterCount>>

\* 2. Loop process waits until its host node is colored
RequireColor(lp) ==
    LET n == CHOOSE node \in Node : <<lp, "loop", node>> \in HostMapping IN
    /\ colors[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = 1]
    /\ UNCHANGED <<colors, msgs, sampleSet, iterCount>>

\* 3. Loop process selects a random sample set and sends queries
QuerySample(lp) ==
    LET n == CHOOSE node \in Node : <<lp, "loop", node>> \in HostMapping IN
    /\ pc[lp] = 1
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = 
          CHOOSE s \in SUBSET (Node \ {n}) :
                Cardinality(s) = SampleSetSize]
    /\ msgs' = msgs
          \cup { [type |-> "Query",
                  src  |-> lp,
                  dst  |-> QueryOf(p),
                  color|-> colors[n],
                  loop |-> lp] :
                 p \in sampleSet'[lp] }
    /\ pc' = [pc EXCEPT ![lp] = 2]
    /\ UNCHANGED <<colors, iterCount>>

\* 4a. Query process receives a query and possibly adopts the color
ReceiveQuery(qp) ==
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst = qp
    LET n == CHOOSE node \in Node : <<qp, "query", node>> \in HostMapping IN
    LET newColor == IF colors[n] = NoColor THEN m.color ELSE colors[n] IN
    /\ colors' = [colors EXCEPT ![n] = newColor]
    /\ msgs' = (msgs \ {m})
         \cup { [type |-> "Reply",
                  src  |-> qp,
                  dst  |-> m.src,
                  color|-> newColor,
                  loop |-> m.loop] }
    /\ UNCHANGED <<pc, sampleSet, iterCount>>

\* 4b. Loop process receives a reply (no state change other than message removal)
ReceiveReply(lp) ==
    /\ \E m \in msgs :
          /\ m.type = "Reply"
          /\ m.dst = lp
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<colors, pc, sampleSet, iterCount>>

\* 5. Loop process tallies replies and possibly flips its node's color
TallyAndFlip(lp) ==
    LET n == CHOOSE node \in Node : <<lp, "loop", node>> \in HostMapping IN
    /\ pc[lp] = 2
    /\ \A p \in sampleSet[lp] :
          \E r \in msgs :
              /\ r.type = "Reply"
              /\ r.dst = lp
              /\ r.src = QueryOf(p)
    LET replies == { r \in msgs :
                      r.type = "Reply" /\ r.dst = lp /\ r.src = QueryOf(p) : r }
        redCount == Cardinality({ r \in replies : r.color = "Red" })
        blueCount == Cardinality({ r \in replies : r.color = "Blue" })
        newColor == 
            IF redCount >= PickFlipThreshold THEN "Red"
            ELSE IF blueCount >= PickFlipThreshold THEN "Blue"
            ELSE colors[n]
    IN
    /\ colors' = [colors EXCEPT ![n] = newColor]
    /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ msgs' = msgs \ { r \in msgs :
                         r.type = "Reply" /\ r.dst = lp }
    /\ pc' = [pc EXCEPT ![lp] = 
                IF iterCount'[lp] < SlushIterationCount THEN 1 ELSE 3]
    /\ UNCHANGED <<>>

\* 6. Loop process termination broadcast
TerminateLoop(lp) ==
    /\ pc[lp] = 3
    /\ msgs' = msgs \cup { [type |-> "Terminate",
                            src  |-> lp,
                            dst  |-> qp,
                            color|-> NoColor,
                            loop |-> lp] :
                           qp \in SlushQueryProcess }
    /\ pc' = [pc EXCEPT ![lp] = 4]
    /\ UNCHANGED <<colors, sampleSet, iterCount>>

\* 7. Query process exits when all loop processes have terminated
QueryExit(qp) ==
    /\ pc[qp] = 0
    /\ \A lp \in SlushLoopProcess : pc[lp] = 4
    /\ pc' = [pc EXCEPT ![qp] = 5]
    /\ UNCHANGED <<colors, msgs, sampleSet, iterCount>>

(***************************************************************************)
(* Next-state relation                                                    *)
(***************************************************************************)
Next ==
    \/ /\ \E n \in Node : colors[n] = NoColor
          /\ ClientAssign
    \/ /\ \E lp \in SlushLoopProcess :
          /\ pc[lp] = 0
          /\ RequireColor(lp)
    \/ /\ \E lp \in SlushLoopProcess :
          /\ pc[lp] = 1
          /\ QuerySample(lp)
    \/ /\ \E qp \in SlushQueryProcess :
          /\ ReceiveQuery(qp)
    \/ /\ \E lp \in SlushLoopProcess :
          /\ pc[lp] = 2
          /\ TallyAndFlip(lp)
    \/ /\ \E lp \in SlushLoopProcess :
          /\ pc[lp] = 3
          /\ TerminateLoop(lp)
    \/ /\ \E qp \in SlushQueryProcess :
          /\ pc[qp] = 0
          /\ QueryExit(qp)
    \/ /\ \E lp \in SlushLoopProcess :
          /\ pc[lp] = 2
          /\ ReceiveReply(lp)

(***************************************************************************)
(* Specification                                                         *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<colors, msgs, pc, sampleSet, iterCount>>

(***************************************************************************)
(* Type invariant (safety property)                                      *)
(***************************************************************************)
TypeInvariant ==
    /\ colors \in [Node -> Colors]
    /\ msgs \subseteq Msg
    /\ pc \in [AllProcs -> Nat]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCount \in [SlushLoopProcess -> Nat]

(***************************************************************************)
(* Theorems (optional, but useful for TLC)                               *)
(***************************************************************************)
THEOREM Spec => []TypeInvariant

=============================================================================