---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,
    SlushLoopProcess,
    SlushQueryProcess,
    HostMapping,
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold,
    NoColor,
    NoMessage

\* ----------------------------------------------------------------------
\*  Colors used by the protocol
Colors == {"Red", "Blue"}

MessageType == {"query", "reply", "term"}

\* ----------------------------------------------------------------------
\*  Helper functions to obtain the node associated with a loop or query
NodeOfLoop(lp) ==
    CHOOSE n \in Node : <<n, lp, q>> \in HostMapping

NodeOfQuery(qp) ==
    CHOOSE n \in Node : <<n, l, qp>> \in HostMapping

QueryProcOf(n) ==
    CHOOSE qp \in SlushQueryProcess : <<n, l, qp>> \in HostMapping

LoopProcOf(n) ==
    CHOOSE lp \in SlushLoopProcess : <<n, lp, q>> \in HostMapping

\* ----------------------------------------------------------------------
\*  Global state variables
VARIABLES
    color,          \* [Node -> (Colors \cup {NoColor})]
    msgs,           \* set of messages
    sample,         \* [SlushLoopProcess -> SUBSET Node]
    iter,           \* [SlushLoopProcess -> Nat]
    pc              \* [Proc -> String]   (process program counter)

vars == <<color, msgs, sample, iter, pc>>

\* ----------------------------------------------------------------------
\*  Nondeterministic choice of a subset of size k
RandomSubset(S, k) ==
    CHOOSE t \in SUBSET S : Cardinality(t) = k

\* ----------------------------------------------------------------------
\*  Initialization
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]
    /\ pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "start"]

\* ----------------------------------------------------------------------
\*  1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ \E n \in Node : color[n] = NoColor
    /\ LET n == CHOOSE n \in Node : color[n] = NoColor
            c == CHOOSE c \in Colors
       IN
          /\ color' = [color EXCEPT ![n] = c]
          /\ UNCHANGED <<msgs, sample, iter, pc>>

\* ----------------------------------------------------------------------
\*  2. Loop process selects a sample and sends query messages
LoopSample ==
    /\ \E lp \in SlushLoopProcess :
          LET n == NodeOfLoop(lp) IN
              /\ color[n] # NoColor
              /\ iter[lp] < SlushIterationCount
              /\ sample[lp] = {}
    /\ LET lp == CHOOSE lp \in SlushLoopProcess :
                LET n == NodeOfLoop(lp) IN
                    /\ color[n] # NoColor
                    /\ iter[lp] < SlushIterationCount
                    /\ sample[lp] = {}
          n == NodeOfLoop(lp)
          s == RandomSubset(Node \ {n}, SampleSetSize)
          qmsgs == { [type |-> "query",
                     src  |-> lp,
                     dst  |-> QueryProcOf(p),
                     col  |-> color[n]] :
                     p \in s }
       IN
          /\ sample' = [sample EXCEPT ![lp] = s]
          /\ msgs'   = msgs \cup qmsgs
          /\ UNCHANGED <<color, iter, pc>>

\* ----------------------------------------------------------------------
\*  3. Query process responds to a query (and may adopt the queried color)
QueryRespond ==
    /\ \E qp \in SlushQueryProcess :
          \E m \in msgs :
               /\ m.type = "query"
               /\ m.dst  = qp
    /\ LET qp == CHOOSE qp \in SlushQueryProcess :
                \E m \in msgs :
                    m.type = "query" /\ m.dst = qp
          m  == CHOOSE m \in msgs :
                    m.type = "query" /\ m.dst = qp
          n  == NodeOfQuery(qp)
          newCol == IF color[n] = NoColor THEN m.col ELSE color[n]
          reply  == [type |-> "reply",
                     src  |-> qp,
                     dst  |-> m.src,
                     col  |-> newCol]
       IN
          /\ color' = [color EXCEPT ![n] = newCol]
          /\ msgs'   = (msgs \ {m}) \cup {reply}
          /\ UNCHANGED <<sample, iter, pc>>

\* ----------------------------------------------------------------------
\*  4. Loop process tallies replies and possibly flips its node's color
LoopTally ==
    /\ \E lp \in SlushLoopProcess :
          LET n == NodeOfLoop(lp) IN
              /\ sample[lp] # {}
              /\ \A p \in sample[lp] :
                     \E r \in msgs :
                         r.type = "reply" /\ r.dst = lp /\ r.src = QueryProcOf(p)
    /\ LET lp == CHOOSE lp \in SlushLoopProcess :
                LET n == NodeOfLoop(lp) IN
                    /\ sample[lp] # {}
                    /\ \A p \in sample[lp] :
                       \E r \in msgs :
                           r.type = "reply" /\ r.dst = lp /\ r.src = QueryProcOf(p)
          reps      == { r \in msgs :
                         r.type = "reply" /\ r.dst = lp }
          redCnt    == Cardinality({ r \in reps : r.col = "Red" })
          blueCnt   == Cardinality({ r \in reps : r.col = "Blue" })
          newCol    == IF redCnt   >= PickFlipThreshold THEN "Red"
                      ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                      ELSE color[n]
       IN
          /\ color'  = [color EXCEPT ![n] = newCol]
          /\ msgs'   = msgs \ reps
          /\ sample' = [sample EXCEPT ![lp] = {}]
          /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
          /\ UNCHANGED pc

\* ----------------------------------------------------------------------
\*  5. Loop process broadcasts termination after finishing all iterations
LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
          /\ iter[lp] = SlushIterationCount
          /\ sample[lp] = {}
          /\ \A m \in msgs : ~(m.type = "term" /\ m.src = lp)
    /\ LET lp == CHOOSE lp \in SlushLoopProcess :
                /\ iter[lp] = SlushIterationCount
                /\ sample[lp] = {}
                /\ \A m \in msgs : ~(m.type = "term" /\ m.src = lp)
          termMsg == [type |-> "term",
                     src  |-> lp,
                     dst  |-> "all",
                     col  |-> NoMessage]
       IN
          /\ msgs' = msgs \cup {termMsg}
          /\ UNCHANGED <<color, sample, iter, pc>>

\* ----------------------------------------------------------------------
\*  6. Query processes exit when all termination messages have been seen
QueryExit ==
    /\ \E qp \in SlushQueryProcess :
          /\ \A m \in msgs : m.type = "term"
    /\ UNCHANGED <<color, msgs, sample, iter, pc>>

\* ----------------------------------------------------------------------
\*  Overall next-state relation
Next ==
    \/ ClientAssign
    \/ LoopSample
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryExit

\* ----------------------------------------------------------------------
\*  Specification
Spec ==
    Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*  Type invariant
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq
        [type : MessageType,
         src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"} \cup {"all"}),
         dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"} \cup {"all"}),
         col  : (Colors \cup {NoColor, NoMessage})]

\* ----------------------------------------------------------------------
\*  (Optional) Liveness: every process eventually reaches a done state
Termination ==
    \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) :
        <> (pc[p] = "done")

\* ----------------------------------------------------------------------
\*  Theorem linking the spec to the invariant
THEOREM Spec => []TypeInvariant

====