---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,                     \* set of nodes
    SlushLoopProcess,         \* set of loop processes (one per node)
    SlushQueryProcess,        \* set of query processes (one per node)
    HostMapping,              \* set of triples [node, loop, query]
    SlushIterationCount,      \* number of iterations each loop process performs
    SampleSetSize,            \* size of the sample set
    PickFlipThreshold,        \* threshold for flipping color
    NoColor,                  \* value representing an uncolored node
    NoMessage                 \* placeholder value for messages without payload

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Color == {"Red", "Blue"}                     \* the two possible colors

\* Functions extracting the components of a host‑mapping triple
NodeOfLoop(lp) == 
    CHOOSE t \in HostMapping : t[2] = lp /\ t[1]

LoopOfNode(n) == 
    CHOOSE t \in HostMapping : t[1] = n /\ t[2]

QueryOfNode(n) == 
    CHOOSE t \in HostMapping : t[1] = n /\ t[3]

NodeOfQuery(qp) == 
    CHOOSE t \in HostMapping : t[3] = qp /\ t[1]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,      \* [Node -> (Color \cup {NoColor})]
    msgs,       \* set of messages in transit
    pc,         \* program counter for each process (including client)
    sample,     \* [SlushLoopProcess -> SUBSET Node] current sample set
    iter        \* [SlushLoopProcess -> Nat] number of completed iterations

vars == << color, msgs, pc, sample, iter >>

\* ----------------------------------------------------------------------
\* Message type
\* ----------------------------------------------------------------------
Message ==
    [type : {"query", "reply", "term"},
     src  : (SlushLoopProcess \cup SlushQueryProcess),
     dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"all"}),
     col  : (Color \cup {NoColor})]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 0]
          \* 0 for client: ready to assign colors
          \* 0 for each loop process: waiting for its node to be colored
          \* 0 for each query process: in its reply loop
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
ClientAssignColor ==
    /\ pc["client"] = 0
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in Color :
          LET newColor == c IN
            /\ color' = [color EXCEPT ![n] = newColor]
            /\ pc'    = [pc EXCEPT !["client"] = 0]
            /\ UNCHANGED << msgs, sample, iter >>
    \/ (* stutter when all nodes are colored *)
       /\ \A n \in Node : color[n] # NoColor
       /\ UNCHANGED << color, msgs, pc, sample, iter >>

\* 2. Loop process waits until its host node is colored
LoopRequireColor(lp) ==
    /\ pc[lp] = 0
    /\ LET n == NodeOfLoop(lp) IN color[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = 1]
    /\ UNCHANGED << color, msgs, sample, iter >>

\* 3. Loop process selects a sample and sends queries
LoopQuerySample(lp) ==
    /\ pc[lp] = 1
    /\ LET n == NodeOfLoop(lp),
           others == Node \ {n},
           sampleSet == CHOOSE s \in SUBSET others :
                         Cardinality(s) = SampleSetSize
       IN
          /\ sample' = [sample EXCEPT ![lp] = sampleSet]
          /\ msgs' = msgs \cup
                       { [type |-> "query",
                          src  |-> lp,
                          dst  |-> QueryOfNode[m],
                          col  |-> color[n]] : m \in sampleSet }
          /\ pc' = [pc EXCEPT ![lp] = 2]
          /\ UNCHANGED << color, iter >>

\* 4. Query process receives a query, possibly adopts the color, and replies
QueryRespond(qp) ==
    /\ pc[qp] = 0
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.dst = qp
          LET srcL == m.src,
              n == NodeOfQuery(qp),
              qcol == m.col,
              curCol == color[n],
              newCol == IF curCol = NoColor THEN qcol ELSE curCol,
              reply == [type |-> "reply",
                        src  |-> qp,
                        dst  |-> srcL,
                        col  |-> newCol]
          IN
             /\ color' = [color EXCEPT ![n] = newCol]
             /\ msgs' = (msgs \ {m}) \cup {reply}
             /\ pc' = [pc EXCEPT ![qp] = 0]   \* stay in reply loop
             /\ UNCHANGED << sample, iter >>

\* 5. Loop process tallies replies and possibly flips its color
LoopTally(lp) ==
    /\ pc[lp] = 2
    /\ LET n == NodeOfLoop(lp),
           sampSet == sample[lp],
           replies == { m \in msgs :
                         /\ m.type = "reply"
                         /\ m.dst = lp
                         /\ m.src \in { QueryOfNode[mn] : mn \in sampSet } },
           cntRed == Cardinality({ m \in replies : m.col = "Red" }),
           cntBlue == Cardinality({ m \in replies : m.col = "Blue" }),
           newCol == IF cntRed >= PickFlipThreshold THEN "Red"
                     ELSE IF cntBlue >= PickFlipThreshold THEN "Blue"
                     ELSE color[n],
           newIter == iter[lp] + 1
        IN
          /\ color' = [color EXCEPT ![n] = newCol]
          /\ iter' = [iter EXCEPT ![lp] = newIter]
          /\ msgs' = msgs \ replies
          /\ sample' = [sample EXCEPT ![lp] = {}]
          /\ pc' = IF newIter = SlushIterationCount
                    THEN [pc EXCEPT ![lp] = 3]   \* go to termination
                    ELSE [pc EXCEPT ![lp] = 1]   \* start next iteration
          /\ UNCHANGED << >>

\* 6. Loop process broadcasts termination
LoopTerminate(lp) ==
    /\ pc[lp] = 3
    /\ msgs' = msgs \cup { [type |-> "term",
                            src  |-> lp,
                            dst  |-> "all",
                            col  |-> NoColor] }
    /\ pc' = [pc EXCEPT ![lp] = 4]    \* done
    /\ UNCHANGED << color, sample, iter >>

\* 7. Query process exits after seeing termination from every loop
QueryExit(qp) ==
    /\ pc[qp] = 0
    /\ \A lp \in SlushLoopProcess :
          \E m \in msgs : /\ m.type = "term" /\ m.src = lp
    /\ pc' = [pc EXCEPT ![qp] = 1]      \* exited state
    /\ UNCHANGED << color, msgs, sample, iter >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssignColor
    \/ \E lp \in SlushLoopProcess : LoopRequireColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopQuerySample(lp)
    \/ \E qp \in SlushQueryProcess : QueryRespond(qp)
    \/ \E lp \in SlushLoopProcess : LoopTally(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (Color \cup {NoColor})]
    /\ msgs  \subseteq Message
    /\ pc    \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> Nat]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [SlushLoopProcess -> Nat]

====