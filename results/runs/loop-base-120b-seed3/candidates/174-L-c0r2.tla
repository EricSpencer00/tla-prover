---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,                 \* Set of node identifiers
    SlushLoopProcess,     \* Set of loop process identifiers (one per node)
    SlushQueryProcess,    \* Set of query process identifiers (one per node)
    HostMapping,          \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,  \* Number of iterations each loop process performs
    SampleSetSize,        \* Size of the peer sample taken each round
    PickFlipThreshold,    \* Minimum number of equal replies needed to flip
    NoColor,              \* Special value meaning “uncolored”
    NoMessage             \* Special placeholder message (unused)

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
Color == {"Red", "Blue"}

Message == [type   : {"query", "reply", "term"},
            src    : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            dst    : (SlushLoopProcess \cup SlushQueryProcess),
            color  : (Color \cup {NoColor})]

\* Functions that retrieve the node, loop, or query process from the mapping
NodeOfLoop(l)   == CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping
NodeOfQuery(q)  == CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping
LoopOfNode(n)   == CHOOSE l \in SlushLoopProcess : \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping
QueryOfNode(n)  == CHOOSE q \in SlushQueryProcess : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    color,      \* [Node -> (Color \cup {NoColor})]
    msgs,       \* Set of in‑flight Message records
    sample,     \* [SlushLoopProcess -> SUBSET SlushQueryProcess]  (current peer sample)
    iter,       \* [SlushLoopProcess -> Nat]  (iterations completed)
    pc          \* [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> {"Init","Done"} ]

vars == <<color, msgs, sample, iter, pc>>

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ iter   = [l \in SlushLoopProcess |-> 0]
    /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "Init"]

\* ----------------------------------------------------------------------
\* ACTIONS
\* ----------------------------------------------------------------------
\* ---- Client assigns a random color to an uncolored node ----------------
ClientAssign ==
    /\ pc["client"] = "Init"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E n \in { n \in Node : color[n] = NoColor } :
          \E c \in Color :
              /\ color' = [color EXCEPT ![n] = c]
              /\ UNCHANGED <<msgs, sample, iter, pc>>
    /\ UNCHANGED pc

ClientDone ==
    /\ pc["client"] = "Init"
    /\ \A n \in Node : color[n] # NoColor
    /\ pc' = [pc EXCEPT !["client"] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* ---- Loop process actions --------------------------------------------
LoopRequireColor(l) ==
    /\ pc[l] = "Init"
    /\ color[NodeOfLoop(l)] # NoColor
    /\ UNCHANGED <<color, msgs, sample, iter, pc>>

LoopSample(l) ==
    /\ pc[l] = "Init"
    /\ color[NodeOfLoop(l)] # NoColor
    /\ sample[l] = {}
    /\ \E peers \in SUBSET (SlushQueryProcess \ { QueryOfNode(NodeOfLoop(l)) }) :
          /\ Cardinality(peers) = SampleSetSize
          /\ sample' = [sample EXCEPT ![l] = peers]
          /\ msgs' = msgs \cup
                     { [type |-> "query",
                        src  |-> l,
                        dst  |-> q,
                        color|-> color[NodeOfLoop(l)]] : q \in peers }
          /\ UNCHANGED <<color, iter, pc>>

LoopTally(l) ==
    /\ pc[l] = "Init"
    /\ sample[l] # {}
    /\ \A q \in sample[l] :
          \E m \in msgs :
              /\ m.type = "reply"
              /\ m.dst  = l
              /\ m.src  = q
    /\ LET
          reds  == Cardinality({ q \in sample[l] :
                \E m \in msgs :
                    /\ m.type = "reply"
                    /\ m.dst  = l
                    /\ m.src  = q
                    /\ m.color = "Red" })
          blues == Cardinality({ q \in sample[l] :
                \E m \in msgs :
                    /\ m.type = "reply"
                    /\ m.dst  = l
                    /\ m.src  = q
                    /\ m.color = "Blue" })
       IN
          IF reds >= PickFlipThreshold THEN
              color' = [color EXCEPT ![NodeOfLoop(l)] = "Red"]
          ELSE IF blues >= PickFlipThreshold THEN
              color' = [color EXCEPT ![NodeOfLoop(l)] = "Blue"]
          ELSE
              UNCHANGED color
    /\ msgs' = (msgs \ { m \in msgs :
                /\ m.dst = l
                /\ m.type = "reply" })
            \cup { m \in msgs :
                /\ m.src = l
                /\ m.type = "query" }    \* remove the queries we sent
    /\ sample' = [sample EXCEPT ![l] = {}]
    /\ iter'   = [iter EXCEPT ![l] = @ + 1]
    /\ UNCHANGED pc

LoopTerminate(l) ==
    /\ pc[l] = "Init"
    /\ iter[l] = SlushIterationCount
    /\ msgs' = msgs \cup
               { [type |-> "term",
                  src  |-> l,
                  dst  |-> lp,
                  color|-> NoColor] : lp \in SlushLoopProcess }
    /\ pc' = [pc EXCEPT ![l] = "Done"]
    /\ UNCHANGED <<color, sample, iter>>

\* ---- Query process actions --------------------------------------------
QueryRespond ==
    /\ \E q \in SlushQueryProcess :
          \E m \in msgs :
              /\ m.type = "query"
              /\ m.dst  = q
              /\ IF color[NodeOfQuery(q)] = NoColor
                    THEN color' = [color EXCEPT ![NodeOfQuery(q)] = m.color]
                    ELSE UNCHANGED color
              /\ msgs' = (msgs \ {m}) \cup
                        { [type |-> "reply",
                           src  |-> q,
                           dst  |-> m.src,
                           color|-> color[NodeOfQuery(q)]] }
              /\ UNCHANGED <<sample, iter, pc>>
    /\ UNCHANGED pc

QueryDone ==
    /\ \A q \in SlushQueryProcess :
          \A lp \in SlushLoopProcess :
              \E m \in msgs :
                  /\ m.type = "term"
                  /\ m.dst  = q
                  /\ m.src  = lp
    /\ pc' = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 
                IF p \in SlushQueryProcess THEN "Done" ELSE pc[p]]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* COMBINED NEXT ACTION
\* ----------------------------------------------------------------------
Next ==
    \/ \E l \in SlushLoopProcess : LoopRequireColor(l)
    \/ \E l \in SlushLoopProcess : LoopSample(l)
    \/ \E l \in SlushLoopProcess : LoopTally(l)
    \/ \E l \in SlushLoopProcess : LoopTerminate(l)
    \/ ClientAssign
    \/ ClientDone
    \/ QueryRespond
    \/ QueryDone

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (Color \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> {"Init","Done"}]

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for TLC checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====