---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node,                \* Set of node identifiers
  SlushLoopProcess,    \* Set of loop process identifiers
  SlushQueryProcess,   \* Set of query process identifiers
  HostMapping,         \* Set of triples <<node, loop, query>>
  SlushIterationCount, \* Number of iterations each loop process performs
  SampleSetSize,       \* Size of the sampled peer set
  PickFlipThreshold,   \* Threshold for flipping a node's color
  NoColor,             \* Special value meaning “uncolored”
  NoMessage            \* Unused placeholder for messages

\* ----------------------------------------------------------------------
\*   Basic Types
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

Message == [type : {"query", "reply", "term"},
            src  : (SlushLoopProcess \cup SlushQueryProcess),
            dst  : (SlushLoopProcess \cup SlushQueryProcess),
            col  : (Colors \cup {NoColor})]

\* ----------------------------------------------------------------------
\*   Helper functions for the host mapping
\* ----------------------------------------------------------------------
HostNodeFromLoop(l) == 
  CHOOSE n \in Node : 
    \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

HostNodeFromQuery(q) ==
  CHOOSE n \in Node :
    \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

LoopOf(node) ==
  CHOOSE l \in SlushLoopProcess :
    \E q \in SlushQueryProcess : <<node, l, q>> \in HostMapping

QueryOf(node) ==
  CHOOSE q \in SlushQueryProcess :
    \E l \in SlushLoopProcess : <<node, l, q>> \in HostMapping

\* ----------------------------------------------------------------------
\*   Variables
\* ----------------------------------------------------------------------
VARIABLES
  colors,          \* [Node -> (Colors \cup {NoColor})]
  msgs,            \* Set of in‑flight messages
  sample,          \* [SlushLoopProcess -> SUBSET Node]
  iter,            \* [SlushLoopProcess -> Nat]  (iterations completed)
  procStateLoop,   \* [SlushLoopProcess -> {"waitColor","waitReplies","done","terminated"}]
  procStateQuery,  \* [SlushQueryProcess -> {"replyLoop","done"}]
  clientState,     \* {"assign","done"}
  termSent         \* SUBSET SlushLoopProcess (loop processes that already sent termination)

\* ----------------------------------------------------------------------
\*   Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ colors = [n \in Node |-> NoColor]
  /\ msgs   = {}
  /\ sample = [l \in SlushLoopProcess |-> {}]
  /\ iter   = [l \in SlushLoopProcess |-> 0]
  /\ procStateLoop = [l \in SlushLoopProcess |-> "waitColor"]
  /\ procStateQuery = [q \in SlushQueryProcess |-> "replyLoop"]
  /\ clientState = "assign"
  /\ termSent = {}

\* ----------------------------------------------------------------------
\*   Actions
\* ----------------------------------------------------------------------
ClientAssign ==
  /\ clientState = "assign"
  /\ \E n \in Node : colors[n] = NoColor
  /\ \E col \in Colors :
        /\ colors' = [colors EXCEPT ![n] = col]
        /\ UNCHANGED <<msgs, sample, iter, procStateLoop, procStateQuery, termSent>>
        /\ IF \A m \in Node : colors'[m] # NoColor
           THEN clientState' = "done"
           ELSE clientState' = "assign"

LoopSample(l) ==
  /\ procStateLoop[l] = "waitColor"
  /\ colors[HostNodeFromLoop(l)] # NoColor
  /\ iter[l] < SlushIterationCount
  /\ \E s \subseteq (Node \ {HostNodeFromLoop(l)}) : Cardinality(s) = SampleSetSize
  /\ sample' = [sample EXCEPT ![l] = s]
  /\ msgs' = msgs \cup
        { [type |-> "query",
           src  |-> l,
           dst  |-> QueryOf(n),
           col  |-> colors[HostNodeFromLoop(l)]] : n \in s }
  /\ UNCHANGED <<colors, iter, procStateQuery, clientState, termSent>>
  /\ procStateLoop' = [procStateLoop EXCEPT ![l] = "waitReplies"]

LoopTally(l) ==
  /\ procStateLoop[l] = "waitReplies"
  /\ \A n \in sample[l] :
        \E m \in msgs :
           m.type = "reply" /\ m.dst = l /\ m.src = QueryOf(n)
  /\ LET
        redCount == Cardinality(
                     { n \in sample[l] :
                       \E m \in msgs :
                         m.type = "reply" /\ m.dst = l /\ m.src = QueryOf(n) /\ m.col = "Red" })
        blueCount == Cardinality(
                     { n \in sample[l] :
                       \E m \in msgs :
                         m.type = "reply" /\ m.dst = l /\ m.src = QueryOf(n) /\ m.col = "Blue" })
        newCol == IF redCount >= PickFlipThreshold THEN "Red"
                 ELSE IF blueCount >= PickFlipThreshold THEN "Blue"
                 ELSE colors[HostNodeFromLoop(l)]
     IN
        /\ colors' = [colors EXCEPT ![HostNodeFromLoop(l)] = newCol]
        /\ sample' = [sample EXCEPT ![l] = {}]
        /\ iter'   = [iter EXCEPT ![l] = @ + 1]
        /\ procStateLoop' = [procStateLoop EXCEPT ![l] =
                               IF @ + 1 = SlushIterationCount THEN "done" ELSE "waitColor"]
        /\ UNCHANGED <<msgs, procStateQuery, clientState, termSent>>

LoopTerminate(l) ==
  /\ procStateLoop[l] = "done"
  /\ l \notin termSent
  /\ msgs' = msgs \cup
        { [type |-> "term",
           src  |-> l,
           dst  |-> q,
           col  |-> NoColor] : q \in SlushQueryProcess }
  /\ termSent' = termSent \cup {l}
  /\ UNCHANGED <<colors, sample, iter, procStateLoop, procStateQuery, clientState>>

QueryRespond(q) ==
  /\ procStateQuery[q] = "replyLoop"
  /\ \E m \in msgs : m.type = "query" /\ m.dst = q
  /\ LET
        m == CHOOSE mm \in msgs : mm.type = "query" /\ mm.dst = q
        n == HostNodeFromQuery(q)
        srcLoop == m.src
        queryCol == m.col
        newColors == IF colors[n] = NoColor THEN [colors EXCEPT ![n] = queryCol] ELSE colors
        replyMsg == [type |-> "reply",
                     src  |-> q,
                     dst  |-> srcLoop,
                     col  |-> newColors[n]]
     IN
        /\ colors' = newColors
        /\ msgs'   = (msgs \ {m}) \cup {replyMsg}
        /\ UNCHANGED <<sample, iter, procStateLoop, procStateQuery, clientState, termSent>>

QueryExit(q) ==
  /\ procStateQuery[q] = "replyLoop"
  /\ clientState = "done"
  /\ \A l \in SlushLoopProcess : l \in termSent
  /\ procStateQuery' = [procStateQuery EXCEPT ![q] = "done"]
  /\ UNCHANGED <<colors, msgs, sample, iter, procStateLoop, clientState, termSent>>

Next ==
  \/ ClientAssign
  \/ \E l \in SlushLoopProcess : LoopSample(l)
  \/ \E l \in SlushLoopProcess : LoopTally(l)
  \/ \E l \in SlushLoopProcess : LoopTerminate(l)
  \/ \E q \in SlushQueryProcess : QueryRespond(q)
  \/ \E q \in SlushQueryProcess : QueryExit(q)

\* ----------------------------------------------------------------------
\*   Specification
\* ----------------------------------------------------------------------
vars == <<colors, msgs, sample, iter, procStateLoop,
          procStateQuery, clientState, termSent>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*   Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ colors \in [Node -> (Colors \cup {NoColor})]
  /\ msgs   \subseteq Message
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iter   \in [SlushLoopProcess -> Nat]
  /\ procStateLoop \in [SlushLoopProcess -> {"waitColor","waitReplies","done","terminated"}]
  /\ procStateQuery \in [SlushQueryProcess -> {"replyLoop","done"}]
  /\ clientState \in {"assign","done"}
  /\ termSent \subseteq SlushLoopProcess

=============================================================================