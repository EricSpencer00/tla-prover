---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,\* set of node identifiers
    SlushLoopProcess,\* set of loop process identifiers
    SlushQueryProcess,\* set of query process identifiers
    HostMapping,\* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,\* number of iterations each loop performs
    SampleSetSize,\* size of the peer sample
    PickFlipThreshold,\* threshold to adopt a color
    NoColor,\* value representing an uncolored node
    NoMessage \* value used in termination messages

\* ----------------------------------------------------------------------
\* Colors and messages
\* ----------------------------------------------------------------------
Color == {"Red", "Blue", NoColor}
MessageType == {"Query", "Reply", "Term"}
Message == [type : MessageType,
            src  : (SlushLoopProcess \cup SlushQueryProcess),
            dst  : (SlushLoopProcess \cup SlushQueryProcess),
            color: Color]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    color,   \* [Node -> Color]
    msgs,    \* SUBSET Message
    sample,  \* [SlushLoopProcess -> SUBSET Node]
    iter,    \* [SlushLoopProcess -> Nat]
    pc       \* [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> PCState]

PCState == {"ClientAssign",
            "LoopWait", "LoopSample", "LoopCollect",
            "LoopTerminate", "LoopDone",
            "QueryLoop", "QueryDone"}

\* ----------------------------------------------------------------------
\* Helper functions to obtain the node associated with a process
\* ----------------------------------------------------------------------
NodeOfLoop(p) ==
    CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping

NodeOfQuery(q) ==
    CHOOSE n \in Node : \E p \in SlushLoopProcess : <<n, p, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]
    /\ pc     = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-
                 CASE proc \in SlushLoopProcess -> "LoopWait"
                      proc \in SlushQueryProcess -> "QueryLoop"
                      proc = "Client"            -> "ClientAssign"]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = "ClientAssign"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in {"Red","Blue"} :
          LET n == CHOOSE n \in Node : color[n] = NoColor
          IN  color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, sample, iter, pc>>

LoopWait(p) ==
    /\ pc[p] = "LoopWait"
    /\ LET n == NodeOfLoop(p) IN color[n] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "LoopSample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

LoopSample(p) ==
    /\ pc[p] = "LoopSample"
    /\ LET n == NodeOfLoop(p) IN TRUE
    /\ \E s \subseteq Node \ {n} :
          /\ Cardinality(s) = SampleSetSize
          /\ sample' = [sample EXCEPT ![p] = s]
    /\ msgs' = msgs \cup
               { [type |-> "Query",
                  src  |-> p,
                  dst  |-> q,
                  color|-> color[n]] :
                 q \in { q \in SlushQueryProcess :
                        NodeOfQuery(q) \in s } }
    /\ pc' = [pc EXCEPT ![p] = "LoopCollect"]
    /\ UNCHANGED <<color, iter>>

LoopCollect(p) ==
    /\ pc[p] = "LoopCollect"
    /\ LET n == NodeOfLoop(p) IN TRUE
    /\ \A q \in { q \in SlushQueryProcess :
                  NodeOfQuery(q) \in sample[p] } :
          \E m \in msgs :
                /\ m.type = "Reply"
                /\ m.dst  = p
                /\ m.src  = q
    /\ LET reds  == { q \in { q \in SlushQueryProcess :
                               NodeOfQuery(q) \in sample[p] } :
                         \E m \in msgs :
                               /\ m.type = "Reply"
                               /\ m.dst  = p
                               /\ m.src  = q
                               /\ m.color = "Red" }
         blues == { q \in { q \in SlushQueryProcess :
                               NodeOfQuery(q) \in sample[p] } :
                         \E m \in msgs :
                               /\ m.type = "Reply"
                               /\ m.dst  = p
                               /\ m.src  = q
                               /\ m.color = "Blue" }
         newcol == IF Cardinality(reds) >= PickFlipThreshold THEN "Red"
                  ELSE IF Cardinality(blues) >= PickFlipThreshold THEN "Blue"
                  ELSE color[n]
       IN
          /\ color' = [color EXCEPT ![n] = newcol]
    /\ iter'   = [iter EXCEPT ![p] = @ + 1]
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ msgs'   = msgs \ { m \in msgs :
                           m.type = "Reply" /\ m.dst = p }
    /\ IF iter'[p] = SlushIterationCount
          THEN pc' = [pc EXCEPT ![p] = "LoopTerminate"]
          ELSE pc' = [pc EXCEPT ![p] = "LoopSample"]
    /\ UNCHANGED <<>>

LoopTerminate(p) ==
    /\ pc[p] = "LoopTerminate"
    /\ msgs' = msgs \cup
               { [type |-> "Term",
                  src  |-> p,
                  dst  |-> q,
                  color|-> NoMessage] :
                 q \in SlushQueryProcess }
    /\ pc' = [pc EXCEPT ![p] = "LoopDone"]
    /\ UNCHANGED <<color, sample, iter>>

QueryLoop(q) ==
    /\ pc[q] = "QueryLoop"
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst  = q
    /\ LET n == NodeOfQuery(q) IN
          IF color[n] = NoColor
               THEN color' = [color EXCEPT ![n] = m.color]
               ELSE color' = color
    /\ msgs' = (msgs \ {m}) \cup
               { [type |-> "Reply",
                  src  |-> q,
                  dst  |-> m.src,
                  color|-> color[n]] }
    /\ pc' = [pc EXCEPT ![q] = "QueryLoop"]
    /\ UNCHANGED <<sample, iter>>

QueryExit(q) ==
    /\ pc[q] = "QueryLoop"
    /\ \A p \in SlushLoopProcess : pc[p] = "LoopDone"
    /\ pc' = [pc EXCEPT ![q] = "QueryDone"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

Next ==
    \/ \E p \in SlushLoopProcess : LoopWait(p)
    \/ \E p \in SlushLoopProcess : LoopSample(p)
    \/ \E p \in SlushLoopProcess : LoopCollect(p)
    \/ \E p \in SlushLoopProcess : LoopTerminate(p)
    \/ \E q \in SlushQueryProcess : QueryLoop(q)
    \/ \E q \in SlushQueryProcess : QueryExit(q)
    \/ ClientAssign

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> Color]
    /\ msgs \subseteq Message

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sample, iter, pc>>

====