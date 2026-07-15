---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets

\* -------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* -------------------------------------------------
CONSTANTS 
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers
    SlushQueryProcess,  \* Set of query process identifiers
    HostMapping,        \* Set of triples [lp |-> p, qp |-> q, n |-> n] linking loop & query processes to a node
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Size of the peer sample each loop process draws
    PickFlipThreshold,  \* Number of matching replies required to flip a node's color
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value meaning "no message"

\* -------------------------------------------------
\* Derived constants
\* -------------------------------------------------
Colors == {"Red", "Blue"}

\* -------------------------------------------------
\* Helper functions on HostMapping
\* -------------------------------------------------
NodeOfLoop(lp) == 
    \E hm \in HostMapping : hm.lp = lp

NodeOfQuery(qp) ==
    \E hm \in HostMapping : hm.qp = qp

LoopOfNode(n) ==
    \E hm \in HostMapping : hm.n = n

QueryOfNode(n) ==
    \E hm \in HostMapping : hm.n = n

\* -------------------------------------------------
\* Message type definition
\* -------------------------------------------------
Message == 
    [type : {"Query", "Reply", "Terminate"},
     src  : (SlushLoopProcess \cup SlushQueryProcess),
     dst  : (SlushLoopProcess \cup SlushQueryProcess),
     payload : (Colors \cup {"None"})]

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES
    nodeColor,      \* [n \in Node |-> NoColor or a color]
    msgs,           \* Set of in‑flight messages
    pc,             \* Program counter per process
    sampleSet,      \* [lp \in SlushLoopProcess |-> {}] – peers currently sampled
    iterCount       \* [lp \in SlushLoopProcess |-> 0] – completed iterations

\* -------------------------------------------------
\* Initialization
\* -------------------------------------------------
Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ msgs       = {}
    /\ pc         = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> "Start"]
    /\ sampleSet  = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount  = [lp \in SlushLoopProcess |-> 0]

\* -------------------------------------------------
\* Actions
\* -------------------------------------------------
\* 1. Client assigns a color to an uncolored node
ClientAssign ==
    /\ pc["Client"] = "Start"
    /\ \E n \in Node :
          /\ nodeColor[n] = NoColor
          /\ \E c \in Colors :
                /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
                /\ pc' = [pc EXCEPT !["Client"] = "Done"]
                /\ UNCHANGED <<msgs, sampleSet, iterCount>>
    \/ /\ \A n \in Node : nodeColor[n] # NoColor
       /\ pc' = [pc EXCEPT !["Client"] = "Done"]
       /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

\* 2. Loop process waits until its node has a color
RequireColor(lp) ==
    /\ pc[lp] = "Start"
    /\ LET n == NodeOfLoop(lp) IN nodeColor[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Iter"]
    /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

\* 3. Loop process samples peers and sends Query messages
LoopQuery(lp) ==
    /\ pc[lp] = "Iter"
    /\ iterCount[lp] < SlushIterationCount
    /\ LET n == NodeOfLoop(lp) IN
        /\ sampleCandidates == Node \ {n}
        /\ sampleSet' = [sampleSet EXCEPT ![lp] = 
            { qp \in SlushQueryProcess : 
                NodeOfQuery(qp) \in sampleCandidates } \cap
            SampleSetSize]  \* Non‑deterministically picks a set of size SampleSetSize
    /\ msgs' = msgs \cup 
        { [type |-> "Query",
           src  |-> lp,
           dst  |-> qp,
           payload |-> nodeColor[n]] :
            qp \in sampleSet'[lp] }
    /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
    /\ UNCHANGED <<nodeColor, iterCount>>

\* 4. Query process responds (and adopts color if uncolored)
QueryRespond(qp) ==
    /\ pc[qp] = "Start"
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst = qp
          /\ LET n == NodeOfQuery(qp)
                 c == m.payload
          IN
            /\ IF nodeColor[n] = NoColor
               THEN nodeColor' = [nodeColor EXCEPT ![n] = c]
               ELSE nodeColor' = nodeColor
            /\ msgs' = (msgs \ {m}) \cup 
                { [type |-> "Reply",
                   src  |-> qp,
                   dst  |-> m.src,
                   payload |-> nodeColor'[n]] }
            /\ pc' = [pc EXCEPT ![qp] = "Start"] \* Remain ready for next query
            /\ UNCHANGED <<sampleSet, iterCount>>
    \/ /\ \A m \in msgs : ~(m.type = "Query" /\ m.dst = qp)
       /\ UNCHANGED <<nodeColor, msgs, pc, sampleSet, iterCount>>

\* 5. Loop process tallies replies and possibly flips its node's color
LoopTally(lp) ==
    /\ pc[lp] = "WaitReplies"
    /\ LET n == NodeOfLoop(lp) IN
        /\ \E replies == { m \in msgs : m.type = "Reply" /\ m.dst = lp } :
             /\ \A qp \in sampleSet[lp] :
                    \E m \in replies : m.src = qp
             /\ LET red   == Cardinality({ m \in replies : m.payload = "Red" })
                blue  == Cardinality({ m \in replies : m.payload = "Blue" })
                newColor == 
                    IF red >= PickFlipThreshold THEN "Red"
                    ELSE IF blue >= PickFlipThreshold THEN "Blue"
                    ELSE nodeColor[n]
             IN
                /\ nodeColor' = [nodeColor EXCEPT ![n] = newColor]
                /\ msgs' = msgs \ replies
                /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
                /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]
                /\ pc' = 
                    IF iterCount[lp] + 1 = SlushIterationCount
                    THEN [pc EXCEPT ![lp] = "Terminate"]
                    ELSE [pc EXCEPT ![lp] = "Iter"]
                /\ UNCHANGED <<pc>>  \* pc already updated above
    \/ /\ \A m \in msgs : ~(m.type = "Reply" /\ m.dst = lp)
       /\ UNCHANGED <<nodeColor, msgs, pc, sampleSet, iterCount>>

\* 6. Loop process sends termination message
LoopTerminate(lp) ==
    /\ pc[lp] = "Terminate"
    /\ msgs' = msgs \cup 
        { [type |-> "Terminate",
           src  |-> lp,
           dst  |-> "AllLoops",
           payload |-> "None"] }
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<nodeColor, sampleSet, iterCount>>

\* 7. Query processes exit when all loops are done
QueryExit(qp) ==
    /\ pc[qp] = "Start"
    /\ \A lp \in SlushLoopProcess : pc[lp] = "Done"
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

\* 8. No‑op stuttering step
Stutter ==
    UNCHANGED <<nodeColor, msgs, pc, sampleSet, iterCount>>

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next ==
    \/ \E n \in Node : ClientAssign
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopQuery(lp)
    \/ \E qp \in SlushQueryProcess : QueryRespond(qp)
    \/ \E lp \in SlushLoopProcess : LoopTally(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ Stutter

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<nodeColor, msgs, pc, sampleSet, iterCount>>

\* -------------------------------------------------
\* Safety invariant (type invariant)
\* -------------------------------------------------
TypeInvariant ==
    /\ \A n \in Node : nodeColor[n] \in Colors \cup {NoColor}
    /\ \A m \in msgs :
          /\ m.type \in {"Query", "Reply", "Terminate"}
          /\ m.src \in (SlushLoopProcess \cup SlushQueryProcess \cup {"AllLoops"})
          /\ m.dst \in (SlushLoopProcess \cup SlushQueryProcess \cup {"AllLoops"})
          /\ IF m.type = "Query"   THEN m.payload \in Colors \cup {NoColor}
             ELSE IF m.type = "Reply" THEN m.payload \in Colors \cup {NoColor}
             ELSE m.payload = "None"
    /\ \A lp \in SlushLoopProcess :
          /\ pc[lp] \in {"Start", "Iter", "WaitReplies", "Terminate", "Done"}
          /\ iterCount[lp] \in 0..SlushIterationCount
          /\ sampleSet[lp] \subseteq SlushQueryProcess
    /\ \A qp \in SlushQueryProcess :
          /\ pc[qp] \in {"Start", "Done"}
    /\ pc["Client"] \in {"Start", "Done"}

\* -------------------------------------------------
\* Theorem (optional, to expose the invariant)
\* -------------------------------------------------
THEOREM Spec => []TypeInvariant

====