---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (declared in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* set of loop process identifiers
    SlushQueryProcess,   \* set of query process identifiers
    HostMapping,         \* set of triples [proc |-> ..., host |-> ...]
    SlushIterationCount, \* total number of iterations each loop process may run
    SampleSetSize,       \* size of the peer sample chosen each round
    PickFlipThreshold,   \* threshold of replies needed to cause a flip
    NoColor,             \* special value representing "uncolored"
    NoMessage            \* special value representing "no message"

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Colors == { "red", "blue", NoColor }

MsgType == {"query", "reply", "terminate"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    nodeColor,          \* [n \in Node |-> Colors]
    messages,           \* set of in‑flight messages
    pc,                 \* [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> Nat]
    sampleSet,          \* [l \in SlushLoopProcess |-> SUBSET Node]
    iterCount           \* [l \in SlushLoopProcess |-> Nat]

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
NodeColor == [n \in Node |-> Colors]

Msg == [type : MsgType,
        src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
        dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
        payload : UNION {Colors, {"none"} }]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ messages   = {}
    /\ pc         = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 0]
    /\ sampleSet  = [l \in SlushLoopProcess |-> {}]
    /\ iterCount  = [l \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
HostOf(p) == 
    IF p \in SlushLoopProcess 
        THEN CHOOSE t \in HostMapping : t.proc = p
    ELSE IF p \in SlushQueryProcess
        THEN CHOOSE t \in HostMapping : t.proc = p
    ELSE "none"

LoopHost(l)   == HostOf(l).host
QueryHost(q)  == HostOf(q).host

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Client assigns a color to an uncolored node
ClientAssign ==
    /\ pc["client"] = 0
    /\ \E n \in Node :
          /\ nodeColor[n] = NoColor
          /\ nodeColor' = [nodeColor EXCEPT ![n] = IF Random(2) = 0 THEN "red" ELSE "blue"]
    /\ UNCHANGED <<messages, pc, sampleSet, iterCount>>
    /\ pc' = [pc EXCEPT !["client"] = 1]

\* 2. Each loop process waits until its host node is colored
RequireColor(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 0
    /\ nodeColor[LoopHost(l)] # NoColor
    /\ pc' = [pc EXCEPT ![l] = 1]
    /\ UNCHANGED <<nodeColor, messages, sampleSet, iterCount>>

\* 3. Loop process picks a sample and sends query messages
QuerySampleSet(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 1
    /\ \A n \in sampleSet[l] : n # LoopHost(l)      \* cannot sample self
    /\ sampleSet' = [sampleSet EXCEPT ![l] = 
          { n \in Node \ {LoopHost(l)} : Random(1..Node) <= SampleSetSize }]
    /\ messages' = messages \cup 
          { [type |-> "query",
             src  |-> l,
             dst  |-> q,
             payload |-> nodeColor[LoopHost(l)] ] :
               q \in SlushQueryProcess :
               QueryHost(q) \in sampleSet'[l] }
    /\ pc' = [pc EXCEPT ![l] = 2]
    /\ UNCHANGED <<nodeColor, iterCount>>

\* 4. Query process responds (and may adopt the queried color if uncolored)
RespondToQuery(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = 0
    /\ \E m \in messages :
          /\ m.type = "query"
          /\ m.dst = q
          /\ LET host == QueryHost(q) IN
                nodeColor' = [nodeColor EXCEPT ![host] = 
                     IF nodeColor[host] = NoColor 
                        THEN m.payload 
                        ELSE nodeColor[host] ]
          /\ messages' = (messages \ {m}) \cup 
                { [type |-> "reply",
                   src  |-> q,
                   dst  |-> m.src,
                   payload |-> nodeColor'[QueryHost(q)] ] }
    /\ pc' = [pc EXCEPT ![q] = 1]
    /\ UNCHANGED <<sampleSet, iterCount>>

\* 5. Loop process tallies replies and possibly flips its node's color
TallyReplies(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 2
    /\ \A r \in messages :
         (r.type = "reply" /\ r.dst = l) => r.payload \in Colors
    /\ LET replies == { r.payload : r \in messages /\ r.type = "reply" /\ r.dst = l } IN
       \* Count occurrences of each color
       redCount   == Cardinality({ n \in replies : n = "red" })
       blueCount  == Cardinality({ n \in replies : n = "blue" })
       newColor   == IF redCount >= PickFlipThreshold THEN "red"
                    ELSE IF blueCount >= PickFlipThreshold THEN "blue"
                    ELSE nodeColor[LoopHost(l)]
    /\ nodeColor' = [nodeColor EXCEPT ![LoopHost(l)] = newColor]
    /\ messages' = messages \ 
          { r \in messages : r.type = "reply" /\ r.dst = l }
    /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
    /\ iterCount' = [iterCount EXCEPT ![l] = @ + 1]
    /\ IF iterCount'[l] = SlushIterationCount
          THEN pc' = [pc EXCEPT ![l] = 3] \* go to termination
          ELSE pc' = [pc EXCEPT ![l] = 0] \* start next round
    /\ UNCHANGED <<pc>>

\* 6. Loop termination broadcast
LoopTerminate(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 3
    /\ messages' = messages \cup 
          { [type |-> "terminate",
             src  |-> l,
             dst  |-> "client",
             payload |-> "none"] }
    /\ pc' = [pc EXCEPT ![l] = 4]
    /\ UNCHANGED <<nodeColor, sampleSet, iterCount>>

\* 7. Query processes exit when all loop processes terminated
QueryExit(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = 1
    /\ \A l \in SlushLoopProcess : pc[l] = 4
    /\ pc' = [pc EXCEPT ![q] = 2]
    /\ UNCHANGED <<nodeColor, messages, sampleSet, iterCount>>

\* 8. Client does nothing after initial assignment
ClientDone ==
    /\ pc["client"] = 1
    /\ UNCHANGED <<nodeColor, messages, pc, sampleSet, iterCount>>

\* Next combines all enabled actions
Next ==
    \/ \E l \in SlushLoopProcess : RequireColor(l)
    \/ \E l \in SlushLoopProcess : QuerySampleSet(l)
    \/ \E q \in SlushQueryProcess : RespondToQuery(q)
    \/ \E l \in SlushLoopProcess : TallyReplies(l)
    \/ \E l \in SlushLoopProcess : LoopTerminate(l)
    \/ \E q \in SlushQueryProcess : QueryExit(q)
    \/ ClientAssign
    \/ ClientDone
    \/ UNCHANGED <<nodeColor, messages, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<nodeColor, messages, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Safety invariant (type checking)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ nodeColor \in [Node -> Colors]
    /\ messages \subseteq
          { [type |-> "query", src |-> SlushLoopProcess, dst |-> SlushQueryProcess,
             payload |-> Colors] } \cup
          { [type |-> "reply", src |-> SlushQueryProcess, dst |-> SlushLoopProcess,
             payload |-> Colors] } \cup
          { [type |-> "terminate", src |-> SlushLoopProcess, dst |-> "client",
             payload |-> "none"] }
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> Nat]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCount \in [SlushLoopProcess -> Nat]

====