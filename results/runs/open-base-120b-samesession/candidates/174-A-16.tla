---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Node,                     \* set of node identifiers
    SlushLoopProcess,         \* one loop process per node
    SlushQueryProcess,        \* one query process per node
    HostMapping,              \* function mapping each process (loop or query) to its host node
    SlushIterationCount,      \* number of iterations each loop process performs
    SampleSetSize,            \* size of the peer sample taken each round
    PickFlipThreshold,        \* number of identical replies needed to flip color
    NoColor,                  \* value representing an uncolored node
    NoMessage                 \* placeholder value for messages that carry no color

\* ----------------------------------------------------------------------
\* Colors used by the protocol
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\* Definition of a message
\*   type : {"query","reply","term"}
\*   from : a loop or query process
\*   to   : a loop or query process
\*   col  : a color or NoColor (used only for query/reply)
\* ----------------------------------------------------------------------
Message ==
    [type : {"query", "reply", "term"},
     from : (SlushLoopProcess \cup SlushQueryProcess),
     to   : (SlushLoopProcess \cup SlushQueryProcess),
     col  : (Colors \cup {NoColor, NoMessage})]

MessageSet == { m \in Message : TRUE }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,   \* [node -> (Colors \cup {NoColor})]
    msgs,    \* set of in‑flight messages
    sample,  \* [loopProcess -> SUBSET Node]   (current peer sample)
    iter     \* [loopProcess -> Nat]           (iterations completed)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
HostNode(p) == HostMapping[p]                     \* node hosting process p
QueryProc(n) == CHOOSE q \in SlushQueryProcess : HostNode(q) = n

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------

\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ \E n \in Node : color[n] = NoColor
    /\ LET n == CHOOSE n \in Node : color[n] = NoColor
           c == CHOOSE c \in Colors
       IN  color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, sample, iter>>

\* 2. Loop process selects a random sample of peers and sends queries
LoopSample(l) ==
    /\ l \in SlushLoopProcess
    /\ let n == HostNode(l) in
          /\ color[n] # NoColor
          /\ iter[l] < SlushIterationCount
          /\ sample[l] = {}
    /\ sample' = [sample EXCEPT ![l] = 
                     CHOOSE s \subseteq Node \ {n} :
                         Cardinality(s) = SampleSetSize]
    /\ msgs' = msgs \cup
               { [type |-> "query",
                  from |-> l,
                  to   |-> q,
                  col  |-> color[n]] :
                 q \in { q \in SlushQueryProcess :
                         HostNode(q) \in sample'[l] } }
    /\ UNCHANGED <<color, iter>>

\* 3. Query process receives a query, possibly adopts its color, and replies
RespondQuery(q) ==
    /\ q \in SlushQueryProcess
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.to   = q
    /\ LET m == CHOOSE m \in msgs :
                 m.type = "query" /\ m.to = q
           n  == HostNode(q) IN
       /\ IF color[n] = NoColor
          THEN color' = [color EXCEPT ![n] = m.col]
          ELSE color' = color
       /\ let reply == [type |-> "reply",
                        from |-> q,
                        to   |-> m.from,
                        col  |-> color'[n]] in
          msgs' = (msgs \ {m}) \cup {reply}
    /\ UNCHANGED <<sample, iter>>

\* 4. Loop process tallies replies and possibly flips its color
LoopTally(l) ==
    /\ l \in SlushLoopProcess
    /\ sample[l] # {}
    /\ \A peer \in sample[l] :
          \E r \in msgs :
              /\ r.type = "reply"
              /\ r.to   = l
              /\ r.from \in { q \in SlushQueryProcess : HostNode(q) = peer }
    /\ LET replies == { r \in msgs :
                           r.type = "reply" /\ r.to = l } IN
       reds  == Cardinality({ r \in replies : r.col = "Red" })
       blues == Cardinality({ r \in replies : r.col = "Blue" })
       n     == HostNode(l)
       newc  == IF reds  >= PickFlipThreshold THEN "Red"
               ELSE IF blues >= PickFlipThreshold THEN "Blue"
               ELSE color[n]
    /\ color' = [color EXCEPT ![n] = newc]
    /\ iter'   = [iter EXCEPT ![l] = @ + 1]
    /\ msgs'   = msgs \ replies
    /\ sample' = [sample EXCEPT ![l] = {}]
    /\ UNCHANGED <<>>

\* 5. Loop process has finished all iterations and broadcasts termination
LoopTerminate(l) ==
    /\ l \in SlushLoopProcess
    /\ iter[l] = SlushIterationCount
    /\ msgs' = msgs \cup
               { [type |-> "term",
                  from |-> l,
                  to   |-> q,
                  col  |-> NoMessage] :
                 q \in SlushQueryProcess }
    /\ UNCHANGED <<color, sample, iter>>

\* 6. Query process exits after receiving termination from every loop process
QueryTerminate(q) ==
    /\ q \in SlushQueryProcess
    /\ \A lp \in SlushLoopProcess :
          \E t \in msgs :
              t.type = "term" /\ t.from = lp /\ t.to = q
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ \E l \in SlushLoopProcess : LoopSample(l)
    \/ \E q \in SlushQueryProcess : RespondQuery(q)
    \/ \E l \in SlushLoopProcess : LoopTally(l)
    \/ \E l \in SlushLoopProcess : LoopTerminate(l)
    \/ \E q \in SlushQueryProcess : QueryTerminate(q)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq MessageSet

=============================================================================