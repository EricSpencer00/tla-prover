---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* One loop process per node
    SlushQueryProcess,  \* One query process per node
    HostMapping,        \* Set of triples [p \in SlushLoopProcess |-> q \in SlushQueryProcess |-> n \in Node]
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Fixed size of the peer sample
    PickFlipThreshold,  \* Threshold for adopting a color
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value meaning "no message"

\* ----------------------------------------------------------------------
\* Derived constant sets (for convenience and readability)
\* ----------------------------------------------------------------------
LoopProc == SlushLoopProcess
QueryProc == SlushQueryProcess
Nodes == Node

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,          \* [n \in Nodes -> NoColor \cup {"Red","Blue"}]
    msgs,           \* Set of in‑flight messages
    pc,             \* [proc \in (LoopProc \cup QueryProc \cup {"Client"}) -> pc state]
    sampleSet,      \* [lp \in LoopProc -> SUBSET Nodes]
    iterCount       \* [lp \in LoopProc -> Nat]   (iterations completed)

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : {"Query", "Reply", "Termination"},
            src  : (LoopProc \cup QueryProc),
            dst  : (LoopProc \cup QueryProc),
            payload : (NoColor \cup {"Red","Blue"})]

\* ----------------------------------------------------------------------
\* Helper operators
\* ----------------------------------------------------------------------
HostOf[p \in LoopProc] == HostMapping[p].loopHost
HostOf[p \in QueryProc] == HostMapping[p].queryHost

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Nodes |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [proc \in (LoopProc \cup QueryProc \cup {"Client"}) |-> "Start"]
    /\ sampleSet = [lp \in LoopProc |-> {}]
    /\ iterCount = [lp \in LoopProc |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssignColor ==
    /\ pc["Client"] = "Start"
    /\ \E n \in Nodes :
         /\ color[n] = NoColor
         /\ LET col == IF Random(2) = 0 THEN "Red" ELSE "Blue" IN
                /\ color' = [color EXCEPT ![n] = col]
                /\ pc'    = [pc EXCEPT !["Client"] = "Start"]
                /\ UNCHANGED << msgs, sampleSet, iterCount >>
    \/ /\ \A n \in Nodes : color[n] # NoColor
       /\ pc' = [pc EXCEPT !["Client"] = "Done"]
       /\ UNCHANGED << color, msgs, sampleSet, iterCount >>

RequireColor(lp) ==
    /\ pc[lp] = "WaitColor"
    /\ color[HostOf[lp]] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED << color, msgs, sampleSet, iterCount >>

QuerySampleSet(lp) ==
    /\ pc[lp] = "Sample"
    /\ iterCount[lp] < SlushIterationCount
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = CHOOSE s \in SUBSET (Nodes \ {HostOf[lp]}) :
                                          Cardinality(s) = SampleSetSize]
    /\ msgs' = msgs \cup
               { [type |-> "Query",
                  src  |-> lp,
                  dst  |-> HostMapping[lp].queryHost,
                  payload |-> color[HostOf[lp]] ] :
                    n \in sampleSet[lp] }
    /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
    /\ UNCHANGED << color, iterCount >>

RespondToQuery(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \E m \in msgs :
         /\ m.type = "Query"
         /\ m.dst = qp
         /\ LET n == HostOf[qp] IN
                /\ color' = IF color[n] = NoColor
                             THEN [color EXCEPT ![n] = m.payload]
                             ELSE color
                /\ msgs' = msgs \cup
                          { [type |-> "Reply",
                             src  |-> qp,
                             dst  |-> m.src,
                             payload |-> color'[n] ] }
                /\ msgs'' = msgs' \ {m}
                /\ UNCHANGED << iterCount, sampleSet, pc >>
                /\ \A lp \in LoopProc :
                     IF lp = m.src
                     THEN pc' = [pc EXCEPT ![lp] = pc[lp]]
                     ELSE pc' = pc
                /\ UNCHANGED << color', msgs'' >>
    /\ UNCHANGED << color, sampleSet, iterCount, pc, msgs >>

TallyReplies(lp) ==
    /\ pc[lp] = "WaitReplies"
    /\ \A n \in sampleSet[lp] :
         \E r \in msgs :
            /\ r.type = "Reply"
            /\ r.dst = lp
            /\ r.src = HostMapping[lp].queryHost
            /\ r.payload # NoMessage
    /\ LET reds   == Cardinality({ r \in msgs :
                                    r.type = "Reply" /\ r.dst = lp /\ r.payload = "Red" })
           blues  == Cardinality({ r \in msgs :
                                    r.type = "Reply" /\ r.dst = lp /\ r.payload = "Blue" })
           curCol == color[HostOf[lp]]
           newCol == IF reds >= PickFlipThreshold THEN "Red"
                    ELSE IF blues >= PickFlipThreshold THEN "Blue"
                    ELSE curCol
        IN
        /\ color' = [color EXCEPT ![HostOf[lp]] = newCol]
        /\ msgs' = { m \in msgs :
                     ~ (m.type = "Reply" /\ m.dst = lp) }
        /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
        /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]
        /\ pc' = [pc EXCEPT ![lp] = IF iterCount'[lp] < SlushIterationCount
                                   THEN "Sample"
                                   ELSE "SendTermination"]
        /\ UNCHANGED << >> 

SendTermination(lp) ==
    /\ pc[lp] = "SendTermination"
    /\ msgs' = msgs \cup { [type |-> "Termination",
                            src  |-> lp,
                            dst  |-> "All",
                            payload |-> NoMessage] }
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED << color, sampleSet, iterCount >>

QueryLoopExit(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \A lp \in LoopProc : pc[lp] = "Done"
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED << color, msgs, sampleSet, iterCount >>

Next ==
    \/ ClientAssignColor
    \/ \E lp \in LoopProc : RequireColor(lp)
    \/ \E lp \in LoopProc : QuerySampleSet(lp)
    \/ \E qp \in QueryProc : RespondToQuery(qp)
    \/ \E lp \in LoopProc : TallyReplies(lp)
    \/ \E lp \in LoopProc : SendTermination(lp)
    \/ \E qp \in QueryProc : QueryLoopExit(qp)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Type invariant (safety property)
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue", NoColor}
MsgTypes == {"Query", "Reply", "Termination"}

TypeInvariant ==
    /\ color \in [Nodes -> Colors]
    /\ msgs \subseteq { [type : MsgTypes,
                         src  : (LoopProc \cup QueryProc),
                         dst  : (LoopProc \cup QueryProc \cup {"All"}),
                         payload : (NoMessage \cup Colors)] }
    /\ pc \in [ (LoopProc \cup QueryProc \cup {"Client"}) -> 
                {"Start","Done","WaitColor","Sample","WaitReplies",
                 "SendTermination","ReplyLoop"} ]
    /\ sampleSet \in [LoopProc -> SUBSET Nodes]
    /\ iterCount \in [LoopProc -> Nat]

\* ----------------------------------------------------------------------
\* Theorem (optional) that the spec implies the invariant
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====