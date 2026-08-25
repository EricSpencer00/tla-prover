---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS 
    Node,                 \* set of node identifiers
    SlushLoopProcess,     \* set of loop process identifiers (one per node)
    SlushQueryProcess,    \* set of query process identifiers (one per node)
    HostMapping,          \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,  \* number of iterations each loop process must perform
    SampleSetSize,        \* size of the peer sample per iteration
    PickFlipThreshold,    \* threshold for adopting a color
    NoColor,              \* special value meaning "uncolored"
    NoMessage             \* placeholder for messages that carry no color

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\* Helper functions to navigate HostMapping
\* ----------------------------------------------------------------------
NodeOfLoop(l) ==
    CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

NodeOfQuery(q) ==
    CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

LoopOfNode(n) ==
    CHOOSE l \in SlushLoopProcess : \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

QueryOfNode(n) ==
    CHOOSE q \in SlushQueryProcess : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* Message definitions
\* ----------------------------------------------------------------------
QueryMsg == [type : "Query", src : SlushLoopProcess, dst : SlushQueryProcess,
             color : Colors]

ReplyMsg == [type : "Reply", src : SlushQueryProcess, dst : SlushLoopProcess,
             color : Colors]

TermMsg  == [type : "Term",  src : SlushLoopProcess, dst : SlushQueryProcess]

Message == QueryMsg \cup ReplyMsg \cup TermMsg

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    color,      \* [node -> Colors \cup {NoColor}]
    msgs,       \* set of in‑flight messages
    pc,         \* program counters for all processes
    sample,     \* [loopProc -> SUBSET Node]   (current peer sample)
    iter,       \* [loopProc -> Nat]           (iterations completed)
    termSeen    \* [queryProc -> SUBSET SlushLoopProcess] (termination msgs received)

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ color   = [n \in Node |-> NoColor]
    /\ msgs    = {}
    /\ pc      = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "Init"]
    /\ sample  = [l \in SlushLoopProcess |-> {}]
    /\ iter    = [l \in SlushLoopProcess |-> 0]
    /\ termSeen = [q \in SlushQueryProcess |-> {}]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E n \in Node, c \in Colors :
          /\ color[n] = NoColor
          /\ color' = [color EXCEPT ![n] = c]
          /\ pc'    = [pc EXCEPT !["client"] = "ClientAssign"]
          /\ UNCHANGED <<msgs, sample, iter, termSeen>>
    \/ \E l \in SlushLoopProcess :
          /\ pc[l] = "WaitColor"
          /\ color[NodeOfLoop(l)] # NoColor
          /\ pc' = [pc EXCEPT ![l] = "Sample"]
          /\ UNCHANGED <<color, msgs, sample, iter, termSeen>>
    \/ \E l \in SlushLoopProcess, s \in SUBSET (Node \ {NodeOfLoop(l)}) :
          /\ pc[l] = "Sample"
          /\ iter[l] < SlushIterationCount
          /\ Cardinality(s) = SampleSetSize
          /\ sample' = [sample EXCEPT ![l] = s]
          /\ msgs' = msgs \cup
                    { [type |-> "Query",
                       src  |-> l,
                       dst  |-> QueryOfNode(n),
                       color|-> color[NodeOfLoop(l)] ] :
                       n \in s }
          /\ pc' = [pc EXCEPT ![l] = "Collect"]
          /\ UNCHANGED <<color, iter, termSeen>>
    \/ \E l \in SlushLoopProcess :
          /\ pc[l] = "Sample"
          /\ iter[l] >= SlushIterationCount
          /\ pc' = [pc EXCEPT ![l] = "Terminate"]
          /\ UNCHANGED <<color, msgs, sample, iter, termSeen>>
    \/ \E l \in SlushLoopProcess :
          /\ pc[l] = "Collect"
          /\ \A n \in sample[l] :
                \E m \in msgs :
                     /\ m.type = "Reply"
                     /\ m.src = QueryOfNode(n)
                     /\ m.dst = l
          /\ LET reds  == Cardinality({ m \in msgs :
                                        m.type = "Reply" /\ m.dst = l /\ m.color = "Red" })
               , blues == Cardinality({ m \in msgs :
                                        m.type = "Reply" /\ m.dst = l /\ m.color = "Blue" })
            IN
               /\ color' = IF reds >= PickFlipThreshold THEN
                               [color EXCEPT ![NodeOfLoop(l)] = "Red"]
                           ELSE IF blues >= PickFlipThreshold THEN
                               [color EXCEPT ![NodeOfLoop(l)] = "Blue"]
                           ELSE
                               color
               /\ msgs'  = msgs \ { m \in msgs :
                                    m.type = "Reply" /\ m.dst = l }
               /\ iter'  = [iter EXCEPT ![l] = @ + 1]
               /\ sample' = [sample EXCEPT ![l] = {}]
               /\ pc'    = [pc EXCEPT ![l] =
                             IF iter[l] + 1 = SlushIterationCount
                             THEN "Terminate" ELSE "Sample"]
               /\ UNCHANGED termSeen
    \/ \E l \in SlushLoopProcess :
          /\ pc[l] = "Terminate"
          /\ msgs' = msgs \cup { [type |-> "Term", src |-> l, dst |-> q] : q \in SlushQueryProcess }
          /\ pc' = [pc EXCEPT ![l] = "Done"]
          /\ UNCHANGED <<color, sample, iter, termSeen>>
    \/ \E q \in SlushQueryProcess, m \in msgs :
          /\ pc[q] \in {"Init","ReplySent"}
          /\ m.type = "Query"
          /\ m.dst = q
          /\ LET n == NodeOfQuery(q) IN
                /\ color' = IF color[n] = NoColor THEN
                               [color EXCEPT ![n] = m.color]
                            ELSE
                               color
                /\ reply = [type |-> "Reply", src |-> q, dst |-> m.src, color |-> color[n]]
                /\ msgs' = (msgs \ {m}) \cup {reply}
                /\ pc'   = [pc EXCEPT ![q] = "ReplySent"]
          /\ UNCHANGED <<sample, iter, termSeen>>
    \/ \E q \in SlushQueryProcess, t \in msgs :
          /\ pc[q] \in {"Init","ReplySent"}
          /\ t.type = "Term"
          /\ t.dst = q
          /\ termSeen' = [termSeen EXCEPT ![q] = @ \cup {t.src}]
          /\ msgs' = msgs \ {t}
          /\ pc' = [pc EXCEPT ![q] =
                    IF termSeen'[q] = SlushLoopProcess
                    THEN "Done" ELSE pc[q]]
          /\ UNCHANGED <<color, sample, iter>>
    \/ \E p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) :
          /\ pc[p] = "Done"
          /\ UNCHANGED <<color, msgs, pc, sample, iter, termSeen>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<color, msgs, pc, sample, iter, termSeen>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
MessageSet == Message

TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs  \subseteq MessageSet
    /\ pc    \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) ->
                    {"Init","ClientAssign","WaitColor","Sample","Collect",
                     "Terminate","Done","ReplySent"} ]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [SlushLoopProcess -> Nat]
    /\ termSeen \in [SlushQueryProcess -> SUBSET SlushLoopProcess]

\* ----------------------------------------------------------------------
\* Liveness (termination) – all processes eventually reach "Done"
\* ----------------------------------------------------------------------
Termination == \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}):
                 <> (pc[p] = "Done")

============================================================================