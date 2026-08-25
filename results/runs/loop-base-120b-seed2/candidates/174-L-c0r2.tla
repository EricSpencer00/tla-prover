---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers
    SlushQueryProcess,   \* Set of query process identifiers
    HostMapping,         \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* Number of iterations each loop process performs
    SampleSetSize,       \* Size of the peer sample taken each round
    PickFlipThreshold,   \* Threshold for adopting a color
    NoColor,             \* Special value meaning “uncolored”
    NoMessage            \* Placeholder for “no message”

\* ----------------------------------------------------------------------
\* Derived sets and helper functions
\* ----------------------------------------------------------------------
Process == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Color == {"Red", "Blue", NoColor}

\* Mapping from a loop process to its host node
LoopNode(lp) ==
    CHOOSE n \in Node :
        \E qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping

\* Mapping from a query process to its host node
QueryNode(qp) ==
    CHOOSE n \in Node :
        \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

\* Mapping from a node to its query process
QueryProc(n) ==
    CHOOSE qp \in SlushQueryProcess :
        \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,   \* [node -> Color]
    msgs,    \* Set of in‑flight messages
    pc,      \* Program counter for each process
    sample,  \* [loopProc -> SUBSET Node]  (current peer sample)
    iter     \* [loopProc -> Nat]          (iterations completed)

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
MessageSet ==
    { [type |-> "query", src |-> Process, dst |-> Process, color |-> Color] } \cup
    { [type |-> "reply", src |-> Process, dst |-> Process, color |-> Color] } \cup
    { [type |-> "term",  src |-> Process, dst |-> Process, color |-> NoColor] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in Process |-> 
                IF p = "Client"          THEN "client_start"
                ELSE IF p \in SlushLoopProcess THEN "loop_wait_color"
                ELSE "query_loop"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = "client_start"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in {"Red", "Blue"} : TRUE
    /\ UNCHANGED <<msgs, pc, sample, iter>>
    /\ color' = [color EXCEPT ![n] = c]

ClientDone ==
    /\ pc["Client"] = "client_start"
    /\ \A n \in Node : color[n] # NoColor
    /\ pc' = [pc EXCEPT !["Client"] = "client_done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

LoopRequireColor ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "loop_wait_color"
        /\ color[LoopNode(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "loop_sample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

LoopSample ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "loop_sample"
        /\ LET others == Node \ {LoopNode(lp)} IN
           \E S \in SUBSET others :
               /\ Cardinality(S) = SampleSetSize
               /\ LET newMsgs == { [type |-> "query",
                                   src  |-> lp,
                                   dst  |-> QueryProc(m),
                                   color |-> color[LoopNode(lp)] ] :
                                   m \in S } IN
                  /\ msgs'   = msgs \cup newMsgs
                  /\ sample' = [sample EXCEPT ![lp] = S]
                  /\ pc'     = [pc EXCEPT ![lp] = "loop_wait_replies"]
                  /\ UNCHANGED <<color, iter>>
    /\ TRUE

RespondQuery ==
    /\ \E qp \in SlushQueryProcess :
        /\ pc[qp] = "query_loop"
        /\ \E m \in msgs :
            /\ m.type = "query"
            /\ m.dst  = qp
            /\ LET n == QueryNode(qp) IN
               /\ color' = IF color[n] = NoColor
                           THEN [color EXCEPT ![n] = m.color]
                           ELSE color
               /\ msgs' = (msgs \ {m}) \cup
                          { [type |-> "reply",
                             src  |-> qp,
                             dst  |-> m.src,
                             color |-> color'[n]] }
               /\ UNCHANGED <<pc, sample, iter>>
    /\ TRUE

TallyReplies ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "loop_wait_replies"
        /\ \A n \in sample[lp] :
            \E r \in msgs :
                /\ r.type = "reply"
                /\ r.dst  = lp
                /\ r.src  = QueryProc(n)
        /\ LET redCnt  == Cardinality({ r \in msgs :
                                         r.type = "reply" /\ r.dst = lp /\ r.color = "Red" }),
               blueCnt == Cardinality({ r \in msgs :
                                         r.type = "reply" /\ r.dst = lp /\ r.color = "Blue" })
           IN
           /\ newCol == IF redCnt >= PickFlipThreshold
                        THEN "Red"
                        ELSE IF blueCnt >= PickFlipThreshold
                             THEN "Blue"
                             ELSE color[LoopNode(lp)]
           /\ color' = [color EXCEPT ![LoopNode(lp)] = newCol]
           /\ msgs' = msgs \ { r \in msgs :
                                 r.type = "reply" /\ r.dst = lp }
           /\ sample' = [sample EXCEPT ![lp] = {}]
           /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
           /\ pc' = [pc EXCEPT ![lp] =
                     IF iter'[lp] < SlushIterationCount
                     THEN "loop_sample"
                     ELSE "loop_done"]
           /\ UNCHANGED <<>>
    /\ TRUE

LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "loop_done"
        /\ msgs' = msgs \cup
                  { [type |-> "term",
                     src  |-> lp,
                     dst  |-> qp,
                     color |-> NoColor] : qp \in SlushQueryProcess }
        /\ pc' = [pc EXCEPT ![lp] = "loop_terminated"]
        /\ UNCHANGED <<color, sample, iter>>

QueryExit ==
    /\ \E qp \in SlushQueryProcess :
        /\ pc[qp] = "query_loop"
        /\ \A lp \in SlushLoopProcess :
            \E t \in msgs :
                /\ t.type = "term"
                /\ t.dst  = qp
                /\ t.src  = lp
        /\ pc' = [pc EXCEPT ![qp] = "query_done"]
        /\ UNCHANGED <<color, msgs, sample, iter>>

Next ==
    \/ ClientAssign
    \/ ClientDone
    \/ LoopRequireColor
    \/ LoopSample
    \/ RespondQuery
    \/ TallyReplies
    \/ LoopTerminate
    \/ QueryExit

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> Color]
    /\ msgs \subseteq MessageSet

====