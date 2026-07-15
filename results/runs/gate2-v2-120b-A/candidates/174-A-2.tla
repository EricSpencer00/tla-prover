---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers
    SlushQueryProcess,   \* Set of query process identifiers
    HostMapping,         \* Set of triples <<lp, qp, n>> linking loop and query processes to a node
    SlushIterationCount, \* Max number of iterations each loop process performs
    SampleSetSize,       \* Size of the peer sample each iteration
    PickFlipThreshold,   \* Threshold of replies needed to flip to a color
    NoColor,             \* Special value meaning "uncolored"
    NoMessage            \* Special value meaning "no pending message"

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    nodeColor,          \* [n \in Node |-> NoColor] or a concrete color
    msgs,               \* Set of in‑flight messages
    pc,                 \* [proc \in SlushLoopProcess \cup SlushQueryProcess \cup {"Client"} |-> pc value]
    sampleSet,          \* [lp \in SlushLoopProcess |-> {}]
    iterCount           \* [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LoopOf(p) == CHOOSE n \in Node : <<p, _, n>> \in HostMapping
QueryOf(p) == CHOOSE n \in Node : <<_, p, n>> \in HostMapping

LoopOfIsDefined == \A p \in SlushLoopProcess : \E n \in Node : <<p, _, n>> \in HostMapping
QueryOfIsDefined == \A p \in SlushQueryProcess : \E n \in Node : <<_, p, n>> \in HostMapping

AllHostTriples == HostMapping

MsgType == {"Query", "Reply", "Terminate"}

Msg ==
    [type : {"Query"},
     src  : SlushLoopProcess,
     dst  : SlushQueryProcess,
     color: Colors] \/
    [type : {"Reply"},
     src  : SlushQueryProcess,
     dst  : SlushLoopProcess,
     color: Colors] \/
    [type : {"Terminate"},
     src  : SlushLoopProcess,
     dst  : SlushLoopProcess]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> "Start"]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]
    /\ LoopOfIsDefined
    /\ QueryOfIsDefined

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssignColor ==
    /\ pc["Client"] = "Start"
    /\ \E n \in Node :
          /\ nodeColor[n] = NoColor
          /\ nodeColor' = [nodeColor EXCEPT ![n] = CHOOSE c \in Colors : TRUE]
    /\ UNCHANGED <<msgs, pc, sampleSet, iterCount>>
    /\ pc' = [pc EXCEPT !["Client"] = "Done"]

LoopRequireColor(lp) ==
    /\ pc[lp] = "RequireColor"
    /\ nodeColor[LoopOf(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

LoopSendQueries(lp) ==
    /\ pc[lp] = "Sample"
    /\ nodeColor[LoopOf(lp)] # NoColor
    /\ sampleSet[lp] = {}
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = { q \in SlushQueryProcess :
                          q # QueryOf(lp) /\ 
                          q \in { QueryOf(p) : p \in SlushLoopProcess } /\
                          Cardinality({ q' \in SlushQueryProcess : q' # q }) = SampleSetSize }]
          \* The above nondeterministically picks any subset of the required size.
    /\ msgs' = msgs \cup { [type |-> "Query",
                           src  |-> lp,
                           dst  |-> q,
                           color|-> nodeColor[LoopOf(lp)]] :
                           q \in sampleSet' }
    /\ pc' = [pc EXCEPT ![lp] = "Collect"]
    /\ UNCHANGED <<nodeColor, iterCount>>

LoopCollectReplies(lp) ==
    /\ pc[lp] = "Collect"
    /\ \A q \in sampleSet[lp] : 
          \E m \in msgs :
              /\ m.type = "Reply"
              /\ m.src = q
              /\ m.dst = lp
    /\ LET replies == { m.color : m \in msgs /\ m.type = "Reply" /\ m.dst = lp } IN
          IF Cardinality(replies) = SampleSetSize
          THEN
             /\ IF \E c \in Colors : 
                    Cardinality({ r \in replies : r = c }) >= PickFlipThreshold
                THEN nodeColor' = [nodeColor EXCEPT ![LoopOf(lp)] = 
                        CHOOSE c \in Colors : 
                            Cardinality({ r \in replies : r = c }) >= PickFlipThreshold]
                ELSE nodeColor' = nodeColor
             /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
             /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
             /\ msgs' = msgs \cup
                 { [type |-> "Terminate",
                    src  |-> lp,
                    dst  |-> lp] }
             /\ pc' = 
                IF iterCount'[lp] < SlushIterationCount
                THEN [pc EXCEPT ![lp] = "Sample"]
                ELSE [pc EXCEPT ![lp] = "Done"]
          ELSE UNCHANGED <<nodeColor, msgs, pc, sampleSet, iterCount>>

QueryRespond(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst = qp
    /\ LET m == CHOOSE mm \in msgs :
            /\ mm.type = "Query"
            /\ mm.dst = qp IN
       /\ nodeColor' = 
            IF nodeColor[LoopOf(QueryOf(qp))] = NoColor
            THEN [nodeColor EXCEPT ![LoopOf(QueryOf(qp))] = m.color]
            ELSE nodeColor
       /\ msgs' = (msgs \ {m}) \cup
            { [type |-> "Reply",
               src  |-> qp,
               dst  |-> m.src,
               color|-> nodeColor'[LoopOf(QueryOf(qp))]] }
       /\ UNCHANGED <<pc, sampleSet, iterCount>>

QueryExit(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \A lp \in SlushLoopProcess : 
          \E m \in msgs : 
               /\ m.type = "Terminate"
               /\ m.src = lp
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

TerminateLoop(lp) ==
    /\ pc[lp] = "Done"
    /\ UNCHANGED <<nodeColor, msgs, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* The overall Next relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E lp \in SlushLoopProcess : LoopRequireColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopSendQueries(lp)
    \/ \E lp \in SlushLoopProcess : LoopCollectReplies(lp)
    \/ \E qp \in SlushQueryProcess : QueryRespond(qp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ TerminateLoop(lp)  \* Allows stuttering after a loop process is done
    \/ ClientAssignColor

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<nodeColor, msgs, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ nodeColor \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq { m \in Msg :
            (m.type = "Query"  => 
                 /\ m.src \in SlushLoopProcess
                 /\ m.dst \in SlushQueryProcess
                 /\ m.color \in Colors) /\
            (m.type = "Reply"  => 
                 /\ m.src \in SlushQueryProcess
                 /\ m.dst \in SlushLoopProcess
                 /\ m.color \in Colors) /\
            (m.type = "Terminate" => 
                 /\ m.src \in SlushLoopProcess
                 /\ m.dst \in SlushLoopProcess) }
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) ->
                {"Start", "RequireColor", "Sample", "Collect", "ReplyLoop", "Done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterCount \in [SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
\* THEOREM stating that the invariant holds (optional, not required by cfg)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====