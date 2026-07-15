---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (must be provided by the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers (one per node)
    SlushQueryProcess,   \* Set of query process identifiers (one per node)
    HostMapping,         \* Set of triples <<proc, "loop"/"query", node>>
    SlushIterationCount, \* Maximum number of iterations each loop process performs
    SampleSetSize,       \* Fixed size of the peer sample drawn each round
    PickFlipThreshold,   \* Minimum number of matching replies needed to flip color
    NoColor,             \* Special value meaning "uncolored"
    NoMessage            \* Special value meaning "no message in transit"

\* ----------------------------------------------------------------------
\* Derived collections
\* ----------------------------------------------------------------------
LoopProcs  == SlushLoopProcess
QueryProcs == SlushQueryProcess
AllProcs   == LoopProcs \cup QueryProcs

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Color == {"Red", "Blue", NoColor}
MsgType == {"query", "reply", "termination"}

Message == [type : MsgType,
            src  : AllProcs,
            dst  : AllProcs,
            payload : UNION {Color, NoMessage}]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,          \* [node -> Color]
    msgs,            \* Set of in‑flight Message
    pc,              \* [proc -> Nat]   program counter (step index)
    sample,          \* [loopProc -> SUBSET Node]  peers sampled this round
    iterCount        \* [loopProc -> Nat]  iterations completed so far

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Host(p) == 
    CASE p \in LoopProcs  -> 
         CHOOSE n \in Node : <<p, "loop", n>> \in HostMapping
         [] p \in QueryProcs ->
         CHOOSE n \in Node : <<p, "query", n>> \in HostMapping
    [] OTHER -> NoMessage

LoopHost(p) ==
    IF p \in LoopProcs THEN Host(p) ELSE NoMessage

QueryHost(p) ==
    IF p \in QueryProcs THEN Host(p) ELSE NoMessage

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors   = [n \in Node |-> NoColor]
    /\ msgs     = {}
    /\ pc       = [proc \in AllProcs |-> 0]
    /\ sample   = [lp \in LoopProcs |-> {}]
    /\ iterCount= [lp \in LoopProcs |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    \E n \in Node :
        /\ colors[n] = NoColor
        /\ \E c \in {"Red", "Blue"} :
            /\ colors' = [colors EXCEPT ![n] = c]
            /\ UNCHANGED <<msgs, pc, sample, iterCount>>

RequireColor(lp) ==
    /\ lp \in LoopProcs
    /\ pc[lp] = 1
    /\ colors[LoopHost(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = 2]
    /\ UNCHANGED <<colors, msgs, sample, iterCount>>

SendQueries(lp) ==
    /\ lp \in LoopProcs
    /\ pc[lp] = 2
    /\ \E s \subseteq Node : 
        /\ s # {LoopHost(lp)}            \* cannot sample self
        /\ Cardinality(s) = SampleSetSize
        /\ \A q \in s : 
               \E qp \in QueryProcs :
                  /\ QueryHost(qp) = q
        /\ sample' = [sample EXCEPT ![lp] = s]
        /\ msgs' = msgs \cup 
            { [type |-> "query",
               src  |-> lp,
               dst  |-> qp,
               payload |-> colors[LoopHost(lp)] ] 
               : qp \in QueryProcs : QueryHost(qp) \in s }
        /\ pc' = [pc EXCEPT ![lp] = 3]
        /\ UNCHANGED <<colors, iterCount>>

ProcessQuery(qp) ==
    /\ qp \in QueryProcs
    /\ \E m \in msgs :
        /\ m.type = "query"
        /\ m.dst = qp
    /\ LET n == QueryHost(qp) IN
       /\ IF colors[n] = NoColor
          THEN colors' = [colors EXCEPT ![n] = m.payload]
          ELSE UNCHANGED colors
    /\ msgs' = (msgs \ {m}) \cup
        { [type |-> "reply",
           src  |-> qp,
           dst  |-> m.src,
           payload |-> colors[LoopHost(m.src)]] }
    /\ UNCHANGED <<pc, sample, iterCount>>

TallyReplies(lp) ==
    /\ lp \in LoopProcs
    /\ pc[lp] = 3
    /\ \A q \in sample[lp] : 
          \E qp \in QueryProcs :
             /\ QueryHost(qp) = q
             /\ \E r \in msgs :
                    /\ r.type = "reply"
                    /\ r.dst = lp
                    /\ r.src = qp
    /\ LET reds   == { r.payload : r \in msgs 
                       /\ r.type = "reply"
                       /\ r.dst = lp
                       /\ r.payload = "Red" }
       blues  == { r.payload : r \in msgs 
                       /\ r.type = "reply"
                       /\ r.dst = lp
                       /\ r.payload = "Blue" } IN
       /\ IF Cardinality(reds) >= PickFlipThreshold
          THEN colors' = [colors EXCEPT ![LoopHost(lp)] = "Red"]
          ELSE IF Cardinality(blues) >= PickFlipThreshold
               THEN colors' = [colors EXCEPT ![LoopHost(lp)] = "Blue"]
               ELSE UNCHANGED colors
    /\ msgs' = msgs \ { r \in msgs : r.type = "reply" /\ r.dst = lp }
    /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]
    /\ pc' = IF iterCount[lp] + 1 >= SlushIterationCount
             THEN [pc EXCEPT ![lp] = 4]   \* go to termination step
             ELSE [pc EXCEPT ![lp] = 2]   \* loop back to next round

SendTermination(lp) ==
    /\ lp \in LoopProcs
    /\ pc[lp] = 4
    /\ msgs' = msgs \cup 
        { [type |-> "termination",
           src  |-> lp,
           dst  |-> qp,
           payload |-> NoMessage] : qp \in QueryProcs }
    /\ pc' = [pc EXCEPT ![lp] = 5]
    /\ UNCHANGED <<colors, sample, iterCount>>

QueryLoopExit(qp) ==
    /\ qp \in QueryProcs
    /\ pc[qp] = 0
    /\ \A lp \in LoopProcs : 
          \E t \in msgs :
              /\ t.type = "termination"
              /\ t.dst = qp
    /\ msgs' = msgs \ { t \in msgs : t.type = "termination" /\ t.dst = qp }
    /\ pc' = [pc EXCEPT ![qp] = 1]
    /\ UNCHANGED <<colors, sample, iterCount>>

LoopDone(lp) ==
    /\ lp \in LoopProcs
    /\ pc[lp] = 5
    /\ UNCHANGED <<colors, msgs, pc, sample, iterCount>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E n \in Node, c \in {"Red","Blue"} : ClientAssign
    \/ \E lp \in LoopProcs : RequireColor(lp)
    \/ \E lp \in LoopProcs : SendQueries(lp)
    \/ \E qp \in QueryProcs : ProcessQuery(qp)
    \/ \E lp \in LoopProcs : TallyReplies(lp)
    \/ \E lp \in LoopProcs : SendTermination(lp)
    \/ \E qp \in QueryProcs : QueryLoopExit(qp)
    \/ \E lp \in LoopProcs : LoopDone(lp)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, pc, sample, iterCount>>

\* ----------------------------------------------------------------------
\* Type invariant (required)
\* ----------------------------------------------------------------------
ColorAssgnOK == [n \in Node |-> colors[n] \in Color]

MsgInSet(m) ==
    /\ m \in msgs
    /\ m.type \in MsgType
    /\ m.src \in AllProcs
    /\ m.dst \in AllProcs
    /\ IF m.type = "query" THEN m.payload \in Color
       ELSE IF m.type = "reply" THEN m.payload \in Color
       ELSE IF m.type = "termination" THEN m.payload = NoMessage
       ELSE FALSE

TypeInvariant == /\ ColorAssgnOK
                 /\ \A m \in msgs : MsgInSet(m)

\* ----------------------------------------------------------------------
\* Theorems (allow TLC to check the invariant)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====