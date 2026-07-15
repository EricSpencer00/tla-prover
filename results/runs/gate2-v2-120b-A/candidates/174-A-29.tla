---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,                \* The set of node identifiers
    SlushLoopProcess,    \* The set of loop process identifiers
    SlushQueryProcess,   \* The set of query process identifiers
    HostMapping,         \* A set of triples [proc |-> p, loop |-> l, query |-> q]
    SlushIterationCount, \* Number of iterations each loop process must perform
    SampleSetSize,       \* Size of the random sample taken each round
    PickFlipThreshold,   \* Threshold of same-colored replies required to flip/adopt
    NoColor,             \* The special value meaning "uncolored"
    NoMessage            \* The special value meaning "no message"

\* ----------------------------------------------------------------------
\* Derived constants (for readability)
\* ----------------------------------------------------------------------
NodeCount == Cardinality(Node)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Color == {"Red", "Blue", NoColor}
MessageType == {"query", "queryReply", "termination"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    nodeColor,          \* [v \in Node -> Color]
    messages,           \* Set of messages currently in flight
    pc,                 \* [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> Nat]
    sampleSet,          \* [l \in SlushLoopProcess -> SUBSET Node]
    iterCount           \* [l \in SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LoopOf(p) == 
    LET mapping == { hm \in HostMapping : hm.proc = p } IN
    IF mapping = {} THEN "none" ELSE CHOOSE hm \in mapping : TRUE

QueryOf(p) == 
    LET mapping == { hm \in HostMapping : hm.proc = p } IN
    IF mapping = {} THEN "none" ELSE CHOOSE hm \in mapping : TRUE

HostNode(p) ==
    LET mapping == { hm \in HostMapping : hm.proc = p } IN
    IF mapping = {} THEN "none" ELSE CHOOSE hm \in mapping : TRUE

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ nodeColor = [v \in Node |-> NoColor]
    /\ messages   = {}
    /\ pc         = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 0]
    /\ sampleSet  = [l \in SlushLoopProcess |-> {}]
    /\ iterCount  = [l \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssignColor ==
    /\ pc["client"] = 0
    /\ \E n \in Node :
          /\ nodeColor[n] = NoColor
          /\ nodeColor' = [nodeColor EXCEPT ![n] = IF RandomBool() THEN "Red" ELSE "Blue"]
    /\ UNCHANGED <<messages, pc, sampleSet, iterCount>>
    /\ pc' = [pc EXCEPT !["client"] = 1]

RequireColor(l) ==
    LET n == HostNode(l) IN
    /\ l \in SlushLoopProcess
    /\ pc[l] = 0
    /\ nodeColor[n] # NoColor
    /\ pc' = [pc EXCEPT ![l] = 1]
    /\ UNCHANGED <<nodeColor, messages, sampleSet, iterCount>>

SendQuery(l) ==
    LET n == HostNode(l) IN
    /\ pc[l] = 1
    /\ nodeColor[n] # NoColor
    /\ sampleSet[l] = {}
    /\ let peers == Node \ {n} in
       let chosen == CHOOSE s \in SUBSET peers : Cardinality(s) = SampleSetSize
       in
       /\ sampleSet' = [sampleSet EXCEPT ![l] = chosen]
    /\ let newMsgs == { [type |-> "query",
                        src  |-> l,
                        dst  |-> q,
                        color|-> nodeColor[n]] :
                        q \in sampleSet[l] } in
       messages' = messages \cup newMsgs
    /\ pc' = [pc EXCEPT ![l] = 2]
    /\ UNCHANGED <<nodeColor, iterCount>>

RespondToQuery(q) ==
    LET n == HostNode(q) IN
    /\ pc[q] = 0
    /\ \E msg \in messages :
          /\ msg.type = "query"
          /\ msg.dst = q
          /\ /\ nodeColor[n] # NoColor
              \/ nodeColor[n] = NoColor /\ nodeColor' = [nodeColor EXCEPT ![n] = msg.color]
          /\ let reply == [type |-> "queryReply",
                           src  |-> q,
                           dst  |-> msg.src,
                           color|-> nodeColor[n]] in
             messages' = (messages \ {msg}) \cup {reply}
    /\ pc' = [pc EXCEPT ![q] = 1]
    /\ UNCHANGED <<sampleSet, iterCount>>

GatherReplies(l) ==
    LET n == HostNode(l) IN
    /\ pc[l] = 2
    /\ \A peer \in sampleSet[l] :
          \E rep \in messages :
              /\ rep.type = "queryReply"
              /\ rep.dst = l
              /\ rep.src = peer
    /\ let reds   == { rep \in messages :
                         /\ rep.type = "queryReply"
                         /\ rep.dst = l
                         /\ rep.color = "Red" } in
       blues  == { rep \in messages :
                         /\ rep.type = "queryReply"
                         /\ rep.dst = l
                         /\ rep.color = "Blue" } in
       /\ (Cardinality(reds) >= PickFlipThreshold) =>
            nodeColor' = [nodeColor EXCEPT ![n] = "Red"]
       /\ (Cardinality(blues) >= PickFlipThreshold) =>
            nodeColor' = [nodeColor EXCEPT ![n] = "Blue"]
       /\ (Cardinality(reds) < PickFlipThreshold /\ Cardinality(blues) < PickFlipThreshold) =>
            UNCHANGED nodeColor
    /\ messages' = messages \ { rep \in messages : rep.type = "queryReply" /\ rep.dst = l }
    /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
    /\ iterCount' = [iterCount EXCEPT ![l] = iterCount[l] + 1]
    /\ pc' = [pc EXCEPT ![l] = 
                IF iterCount[l] + 1 = SlushIterationCount THEN 3 ELSE 1]
    /\ UNCHANGED <<pc, nodeColor>>

LoopTerminate(l) ==
    LET n == HostNode(l) IN
    /\ pc[l] = 3
    /\ messages' = messages \cup { [type |-> "termination", src |-> l, dst |-> "broadcast"] }
    /\ pc' = [pc EXCEPT ![l] = 4]
    /\ UNCHANGED <<nodeColor, sampleSet, iterCount>>

QueryExit(q) ==
    /\ pc[q] = 1
    /\ \A l \in SlushLoopProcess : pc[l] = 4
    /\ pc' = [pc EXCEPT ![q] = 2]
    /\ UNCHANGED <<nodeColor, messages, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Stuttering step to avoid deadlock
\* ----------------------------------------------------------------------
Stutter ==
    UNCHANGED <<nodeColor, messages, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssignColor
    \/ \E l \in SlushLoopProcess : RequireColor(l)
    \/ \E l \in SlushLoopProcess : SendQuery(l)
    \/ \E q \in SlushQueryProcess : RespondToQuery(q)
    \/ \E l \in SlushLoopProcess : GatherReplies(l)
    \/ \E l \in SlushLoopProcess : LoopTerminate(l)
    \/ \E q \in SlushQueryProcess : QueryExit(q)
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<nodeColor, messages, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ nodeColor \in [Node -> Color]
    /\ messages \subseteq {
            [type |-> "query", src |-> SlushLoopProcess, dst |-> SlushQueryProcess, color |-> Color] \/
            [type |-> "queryReply", src |-> SlushQueryProcess, dst |-> SlushLoopProcess, color |-> Color] \/
            [type |-> "termination", src |-> SlushLoopProcess, dst |-> "broadcast", color |-> NoColor]
        }
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> Nat ]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCount \in [SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
\* THEOREM (optional, to aid model checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====