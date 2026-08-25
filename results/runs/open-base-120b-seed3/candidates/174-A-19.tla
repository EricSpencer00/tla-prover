---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be defined in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS 
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers
    SlushQueryProcess,  \* Set of query process identifiers
    HostMapping,        \* Set of triples [loop, query, node]
    SlushIterationCount,\* Number of iterations each loop process must execute
    SampleSetSize,      \* Fixed size of the peer sample
    PickFlipThreshold,  \* Minimum number of equal replies needed to flip
    NoColor,            \* Special value for an uncolored node
    NoMessage           \* Special value for messages that carry no color

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
ColorSet == {"Red", "Blue"}          \* the two possible colors

\* ----------------------------------------------------------------------
\* Helper functions for the host mapping
\* ----------------------------------------------------------------------
NodeOfLoop(p) == 
    CHOOSE hm \in HostMapping : hm.loop = p /\ hm.node

NodeOfQuery(q) ==
    CHOOSE hm \in HostMapping : hm.query = q /\ hm.node

QueryProcOf(n) ==
    CHOOSE hm \in HostMapping : hm.node = n /\ hm.query

\* ----------------------------------------------------------------------
\* Message definitions
\* ----------------------------------------------------------------------
Message == 
    [type : {"query", "reply", "term"},
     src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
     dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"AllQuery"}),
     col  : (ColorSet \cup {NoColor, NoMessage})]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    color,      \* [node \in Node |-> ColorSet \cup {NoColor}]
    msgs,       \* set of messages in transit
    sample,     \* [p \in SlushLoopProcess |-> SUBSET Node]  (current sample of a loop)
    iter,       \* [p \in SlushLoopProcess |-> Nat]          (iterations done)
    doneLoop,   \* subset of SlushLoopProcess that have terminated
    doneQuery,  \* subset of SlushQueryProcess that have exited
    clientDone  \* Boolean indicating the client finished assigning colors

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]
    /\ doneLoop = {}
    /\ doneQuery = {}
    /\ clientDone = FALSE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ ~clientDone
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ c \in ColorSet
          /\ color' = [color EXCEPT ![n] = c]
          /\ UNCHANGED <<msgs, sample, iter, doneLoop, doneQuery>>
          /\ IF \A m \in Node : color'[m] # NoColor
                THEN clientDone' = TRUE
                ELSE clientDone' = FALSE

\* 2. Loop process selects a random sample of peers and sends queries
SamplePeers ==
    /\ \E p \in SlushLoopProcess :
          /\ p \notin doneLoop
          /\ iter[p] < SlushIterationCount
          /\ sample[p] = {}
          /\ let n == NodeOfLoop(p) in
                /\ S \subseteq Node \ {n}
                /\ Cardinality(S) = SampleSetSize
                /\ sample' = [sample EXCEPT ![p] = S]
                /\ msgs' = msgs \cup 
                    { [type |-> "query",
                       src  |-> p,
                       dst  |-> QueryProcOf(s),
                       col  |-> color[n] ] : s \in S }
                /\ UNCHANGED <<color, iter, doneLoop, doneQuery, clientDone>>
          /\ other variables unchanged

\* 3. Query process responds to a query (adopting the color if uncolored)
RespondQuery ==
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ let q == m.dst in
                /\ let n == NodeOfQuery(q) in
                     /\ IF color[n] = NoColor
                           THEN color' = [color EXCEPT ![n] = m.col]
                           ELSE UNCHANGED color
                     /\ msgs' = (msgs \ {m}) \cup 
                         { [type |-> "reply",
                            src  |-> q,
                            dst  |-> m.src,
                            col  |-> (IF color[n] = NoColor THEN m.col ELSE color[n]) ] }
                     /\ UNCHANGED <<sample, iter, doneLoop, doneQuery, clientDone>>

\* 4. Loop process tallies replies and possibly flips its color
TallyReplies ==
    /\ \E p \in SlushLoopProcess :
          /\ p \notin doneLoop
          /\ sample[p] # {}
          /\ let n  == NodeOfLoop(p) in
                /\ let replies == { r \in msgs :
                                      r.type = "reply" /\ r.dst = p } in
                /\ Cardinality(replies) = Cardinality(sample[p])
                /\ cntRed  == Cardinality({ r \in replies : r.col = "Red" })
                /\ cntBlue == Cardinality({ r \in replies : r.col = "Blue" })
                /\ newCol == 
                       IF cntRed >= PickFlipThreshold THEN "Red"
                       ELSE IF cntBlue >= PickFlipThreshold THEN "Blue"
                       ELSE color[n]
                /\ color'  = [color EXCEPT ![n] = newCol]
                /\ iter'   = [iter EXCEPT ![p] = iter[p] + 1]
                /\ sample' = [sample EXCEPT ![p] = {}]
                /\ msgs'   = msgs \ replies
                /\ UNCHANGED <<doneLoop, doneQuery, clientDone>>

\* 5. Loop process terminates after completing all iterations
LoopTerminate ==
    /\ \E p \in SlushLoopProcess :
          /\ p \notin doneLoop
          /\ iter[p] = SlushIterationCount
          /\ doneLoop' = doneLoop \cup {p}
          /\ msgs' = msgs \cup 
                { [type |-> "term",
                   src  |-> p,
                   dst  |-> "AllQuery",
                   col  |-> NoMessage] }
          /\ UNCHANGED <<color, sample, iter, doneQuery, clientDone>>

\* 6. Query processes exit when they have seen termination from all loops
QueryExit ==
    /\ \E q \in SlushQueryProcess :
          /\ q \notin doneQuery
          /\ \A p \in SlushLoopProcess :
                 [type |-> "term", src |-> p, dst |-> "AllQuery", col |-> NoMessage] \in msgs
          /\ doneQuery' = doneQuery \cup {q}
          /\ UNCHANGED <<color, msgs, sample, iter, doneLoop, clientDone>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ SamplePeers
    \/ RespondQuery
    \/ TallyReplies
    \/ LoopTerminate
    \/ QueryExit

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<color, msgs, sample, iter, doneLoop, doneQuery, clientDone>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
MessageInvariant ==
    msgs \subseteq Message

ColorInvariant ==
    color \in [Node -> (ColorSet \cup {NoColor})]

SampleInvariant ==
    sample \in [SlushLoopProcess -> SUBSET Node]

IterInvariant ==
    iter \in [SlushLoopProcess -> Nat]

DoneInvariant ==
    /\ doneLoop \subseteq SlushLoopProcess
    /\ doneQuery \subseteq SlushQueryProcess
    /\ clientDone \in BOOLEAN

TypeInvariant == 
    /\ ColorInvariant
    /\ MessageInvariant
    /\ SampleInvariant
    /\ IterInvariant
    /\ DoneInvariant

\* ----------------------------------------------------------------------
\* THEOREM (optional, can be checked with TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====