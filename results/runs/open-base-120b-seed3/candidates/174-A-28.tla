---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Node,               \* set of node identifiers
    SlushLoopProcess,   \* set of loop process identifiers
    SlushQueryProcess,  \* set of query process identifiers
    HostMapping,        \* set of triples <<proc, "loop"|"query", node>>
    SlushIterationCount,\* number of iterations each loop process performs
    SampleSetSize,      \* size of the peer sample
    PickFlipThreshold,  \* threshold for flipping color
    NoColor,            \* sentinel for an uncolored node
    NoMessage           \* sentinel for "no message"

\* ----------------------------------------------------------------------
\* Additional constants for the two possible colors
CONSTANTS Red, Blue

\* ----------------------------------------------------------------------
\* State variables
VARIABLES 
    color,   \* [node -> Red \/ Blue \/ NoColor]
    msgs,    \* set of in‑flight messages
    sample,  \* [loopProc -> SUBSET Node]   (current peer sample)
    iter     \* [loopProc -> Nat]          (iterations completed)

\* ----------------------------------------------------------------------
\* Helper functions to extract the node hosted by a process
HostNodeLoop(lp) == 
    CHOOSE n \in Node : <<lp, "loop", n>> \in HostMapping

HostNodeQuery(qp) ==
    CHOOSE n \in Node : <<qp, "query", n>> \in HostMapping

QueryProcOfNode(n) ==
    CHOOSE qp \in SlushQueryProcess : <<qp, "query", n>> \in HostMapping

\* ----------------------------------------------------------------------
\* Shape of a message
Message == 
    [type   : {"query", "reply", "term"},
     src    : (SlushLoopProcess \cup SlushQueryProcess),
     dst    : (SlushLoopProcess \cup SlushQueryProcess \cup {"all"}),
     color  : (Red \cup Blue \cup {NoColor})]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
AssignColor ==
    /\ \E n \in Node : color[n] = NoColor
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ \/ color' = [color EXCEPT ![n] = Red]
             \/ color' = [color EXCEPT ![n] = Blue]
    /\ UNCHANGED <<msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* 2. Loop process samples peers and sends queries
SendQuery ==
    /\ \E lp \in SlushLoopProcess :
          LET n == HostNodeLoop(lp) IN
          /\ color[n] # NoColor
          /\ sample[lp] = {}                     \* not currently sampling
          LET peers == Node \ {n}
              chosen == CHOOSE s \in SUBSET peers :
                         Cardinality(s) = SampleSetSize
          IN
              /\ sample' = [sample EXCEPT ![lp] = chosen]
              /\ msgs'   = msgs \cup 
                             { [type |-> "query",
                                src  |-> lp,
                                dst  |-> QueryProcOfNode(p),
                                color|-> color[n]] : p \in chosen }
    /\ UNCHANGED <<color, iter>>

\* ----------------------------------------------------------------------
\* 3. Query process receives a query, possibly adopts the color, and replies
ReceiveQuery ==
    /\ \E qp \in SlushQueryProcess :
          /\ \E m \in msgs :
                /\ m.type = "query"
                /\ m.dst  = qp
                LET n == HostNodeQuery(qp) IN
                /\ IF color[n] = NoColor
                      THEN color' = [color EXCEPT ![n] = m.color]
                      ELSE color' = color
                /\ msgs' = (msgs \ {m}) \cup
                           { [type |-> "reply",
                              src  |-> qp,
                              dst  |-> m.src,
                              color|-> color[n]] }
    /\ UNCHANGED <<sample, iter>>

\* ----------------------------------------------------------------------
\* 4. Loop process tallies replies, possibly flips color, clears sample, increments iteration
FlipAndIterate ==
    /\ \E lp \in SlushLoopProcess :
          LET n      == HostNodeLoop(lp)
              peers  == sample[lp]
          IN
              /\ peers # {}                                          \* a sample exists
              /\ \A p \in peers :
                     \E r \in msgs :
                         /\ r.type = "reply"
                         /\ r.dst  = lp
                         /\ r.src  = QueryProcOfNode(p)
              LET reds  == { r \in msgs : r.type = "reply" /\ r.dst = lp /\ r.color = Red }
                  blues == { r \in msgs : r.type = "reply" /\ r.dst = lp /\ r.color = Blue }
              IN
                  /\ IF Cardinality(reds) >= PickFlipThreshold
                        THEN color' = [color EXCEPT ![n] = Red]
                     ELSE IF Cardinality(blues) >= PickFlipThreshold
                        THEN color' = [color EXCEPT ![n] = Blue]
                     ELSE color' = color
                  /\ sample' = [sample EXCEPT ![lp] = {}]
                  /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
                  /\ msgs'   = msgs \ { r \in msgs : r.type = "reply" /\ r.dst = lp }
    /\ UNCHANGED <<NoMessage>>   \* placeholder to keep the identifier

\* ----------------------------------------------------------------------
\* 5. After completing all iterations, the loop process broadcasts termination
SendTerm ==
    /\ \E lp \in SlushLoopProcess :
          /\ iter[lp] = SlushIterationCount
          /\ msgs' = msgs \cup 
                     { [type |-> "term",
                        src  |-> lp,
                        dst  |-> "all",
                        color|-> NoColor] }
    /\ UNCHANGED <<color, sample, iter>>

\* ----------------------------------------------------------------------
\* 6. Query processes exit when every loop process has sent a termination message
TerminateQuery ==
    /\ \A qp \in SlushQueryProcess :
          /\ \A lp \in SlushLoopProcess :
                \E m \in msgs :
                    /\ m.type = "term"
                    /\ m.src  = lp
    /\ UNCHANGED <<color, sample, iter, msgs>>

\* ----------------------------------------------------------------------
Next ==
    \/ AssignColor
    \/ SendQuery
    \/ ReceiveQuery
    \/ FlipAndIterate
    \/ SendTerm
    \/ TerminateQuery

\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (Red \cup Blue \cup {NoColor})]
    /\ msgs   \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [SlushLoopProcess -> Nat]

=============================================================================