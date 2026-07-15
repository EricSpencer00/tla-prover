---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples [proc |-> p, type |-> "loop" or "query", node |-> n]
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Size of the peer sample each iteration
    PickFlipThreshold,  \* Minimum number of matching replies to trigger a flip
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value meaning "no message"

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
LoopProcs  == { p \in SlushLoopProcess : 
                \E m \in HostMapping : m.type = "loop" /\ m.proc = p }
QueryProcs == { q \in SlushQueryProcess : 
                \E m \in HostMapping : m.type = "query" /\ m.proc = q }

\* ----------------------------------------------------------------------
\* Message type definition
\* ----------------------------------------------------------------------
Message == 
    [type : {"query", "reply", "term"},
     src  : (SlushLoopProcess \cup SlushQueryProcess),
     dst  : (SlushLoopProcess \cup SlushQueryProcess),
     color: NoColor \cup {"Red", "Blue"}]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,          \* [node -> NoColor or "Red"/"Blue"]
    msgs,           \* Set of in‑flight messages
    pc,             \* [proc -> program counter label]
    sample,         \* [loopProc -> SUBSET Node]  (current peer sample)
    iterCount       \* [loopProc -> Nat]  (iterations completed)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NodeOfLoop(p) == 
    CHOOSE m \in HostMapping : m.type = "loop" /\ m.proc = p

NodeOfQuery(q) == 
    CHOOSE m \in HostMapping : m.type = "query" /\ m.proc = q

LoopOfNode(n) == 
    CHOOSE m \in HostMapping : m.type = "loop" /\ m.node = n

QueryOfNode(n) == 
    CHOOSE m \in HostMapping : m.type = "query" /\ m.node = n

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 
                IF p \in SlushLoopProcess THEN "WaitColor"
                ELSE IF p \in SlushQueryProcess THEN "ReplyLoop"
                ELSE "Assign"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = "Assign"
    /\ \E n \in Node :
        /\ color[n] = NoColor
        /\ \E col \in {"Red", "Blue"} :
            /\ color' = [color EXCEPT ![n] = col]
            /\ pc' = [pc EXCEPT !["Client"] = "Assign"]
            /\ UNCHANGED <<msgs, sample, iterCount>>
    \/ /\ \A n \in Node : color[n] # NoColor
       /\ pc' = [pc EXCEPT !["Client"] = "Done"]
       /\ UNCHANGED <<color, msgs, sample, iterCount>>

LoopWaitColor(lp) ==
    /\ pc[lp] = "WaitColor"
    /\ LET n == NodeOfLoop(lp) IN
       /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = "Sample"]
       /\ UNCHANGED <<color, msgs, sample, iterCount>>

LoopSample(lp) ==
    /\ pc[lp] = "Sample"
    /\ LET n == NodeOfLoop(lp) IN
       /\ sample[lp] = {}
       /\ \E s \in SUBSET (Node \ {n}) :
            /\ Cardinality(s) = SampleSetSize
            /\ sample' = [sample EXCEPT ![lp] = s]
            /\ msgs' = msgs \cup 
               { [type |-> "query",
                  src  |-> lp,
                  dst  |-> QueryOfNode(p),
                  color|-> color[n]] : p \in s }
            /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
            /\ UNCHANGED <<color, iterCount>>

LoopWaitReplies(lp) ==
    /\ pc[lp] = "WaitReplies"
    /\ LET n == NodeOfLoop(lp) IN
       /\ \A p \in sample[lp] :
            \E m \in msgs :
                /\ m.type = "reply"
                /\ m.src = QueryOfNode(p)
                /\ m.dst = lp
       /\ \E reds \in Nat, blues \in Nat :
            /\ reds + blues = Cardinality(sample[lp])
            /\ reds = Cardinality({ p \in sample[lp] :
                \E m \in msgs :
                    /\ m.type = "reply"
                    /\ m.src = QueryOfNode(p)
                    /\ m.dst = lp
                    /\ m.color = "Red" })
            /\ blues = Cardinality({ p \in sample[lp] :
                \E m \in msgs :
                    /\ m.type = "reply"
                    /\ m.src = QueryOfNode(p)
                    /\ m.dst = lp
                    /\ m.color = "Blue" })
            /\ IF reds >= PickFlipThreshold THEN
                   color' = [color EXCEPT ![n] = "Red"]
               ELSE IF blues >= PickFlipThreshold THEN
                   color' = [color EXCEPT ![n] = "Blue"]
               ELSE
                   color' = color
            /\ msgs' = { m \in msgs :
                         /\ ~(m.type = "reply" /\ m.dst = lp /\ m.src \in {QueryOfNode(p) : p \in sample[lp]}) }
            /\ sample' = [sample EXCEPT ![lp] = {}]
            /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
            /\ IF iterCount'[lp] = SlushIterationCount THEN
                   pc' = [pc EXCEPT ![lp] = "Terminate"]
               ELSE
                   pc' = [pc EXCEPT ![lp] = "Sample"]
            /\ UNCHANGED <<color, pc, msgs, sample, iterCount>> \* (color already updated above)

LoopTerminate(lp) ==
    /\ pc[lp] = "Terminate"
    /\ msgs' = msgs \cup { [type |-> "term", src |-> lp, dst |-> "All", color |-> NoColor] }
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sample, iterCount>>

QueryReply(q) ==
    /\ pc[q] = "ReplyLoop"
    /\ \E m \in msgs :
        /\ m.type = "query"
        /\ m.dst = q
        /\ LET n == NodeOfQuery(q) IN
           /\ IF color[n] = NoColor THEN
                 color' = [color EXCEPT ![n] = m.color]
              ELSE
                 color' = color
           /\ msgs' = msgs \cup 
               { [type |-> "reply",
                  src  |-> q,
                  dst  |-> m.src,
                  color|-> color'[n]] }
           /\ msgs'' = msgs' \ {m}
           /\ UNCHANGED <<sample, iterCount, pc>>
    \/ /\ \A m \in msgs : ~(m.type = "query" /\ m.dst = q)
       /\ UNCHANGED <<color, msgs, sample, iterCount, pc>>

QueryExit(q) ==
    /\ pc[q] = "ReplyLoop"
    /\ \A lp \in SlushLoopProcess : pc[lp] = "Done"
    /\ pc' = [pc EXCEPT ![q] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iterCount>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : LoopWaitColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopSample(lp)
    \/ \E lp \in SlushLoopProcess : LoopWaitReplies(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E q \in SlushQueryProcess : QueryReply(q)
    \/ \E q \in SlushQueryProcess : QueryExit(q)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iterCount>>

\* ----------------------------------------------------------------------
\* Type invariant (the only required invariant)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (NoColor \cup {"Red", "Blue"})]
    /\ msgs \subseteq Message
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> 
                {"Assign","Done","WaitColor","Sample","WaitReplies","Terminate","ReplyLoop"} ]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCount \in [SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
\* Theorem (optional, not required by the .cfg)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====