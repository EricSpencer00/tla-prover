---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers
    SlushQueryProcess,  \* Set of query process identifiers
    HostMapping,        \* Set of triples <<loopProc, queryProc, node>>
    SlushIterationCount,\* Number of iterations each loop process performs
    SampleSetSize,      \* Size of the peer sample per iteration
    PickFlipThreshold, \* Threshold of same‑color replies needed to flip
    NoColor,            \* Special value meaning “uncolored”
    NoMessage           \* Special value representing the absence of a message

\* ----------------------------------------------------------------------
\* Derived sets and helper functions
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue", NoColor}

\* Mapping from a loop process to its hosted node
LoopNode == [lp \in SlushLoopProcess |-> 
                CHOOSE t \in HostMapping : t[1] = lp |> t[3]]

\* Mapping from a query process to its hosted node
QueryNode == [qp \in SlushQueryProcess |-> 
                CHOOSE t \in HostMapping : t[2] = qp |> t[3]]

\* Mapping from a node to its loop process (bijection assumed)
NodeLoop == [n \in Node |-> 
                CHOOSE t \in HostMapping : t[3] = n |> t[1]]

\* Mapping from a node to its query process (bijection assumed)
NodeQuery == [n \in Node |-> 
                CHOOSE t \in HostMapping : t[3] = n |> t[2]]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,          \* [Node -> Colors] current color of each node
    msgs,           \* Set of messages currently in‑flight
    loopIter,       \* [SlushLoopProcess -> Nat] iteration counter per loop
    loopSample,     \* [SlushLoopProcess -> SUBSET Node] current sample set
    clientReady     \* Boolean flag: TRUE when client may assign a new color

\* Message record definition
Message == [type   : {"query", "reply", "term"},
            from   : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
            to     : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
            color  : Colors]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ loopIter = [lp \in SlushLoopProcess |-> 0]
    /\ loopSample = [lp \in SlushLoopProcess |-> {}]
    /\ clientReady = TRUE

\* ----------------------------------------------------------------------
\* Helper: choose a random color (nondeterministic)
\* ----------------------------------------------------------------------
RandomColor == CHOOSE c \in {"Red", "Blue"} : TRUE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------

\* 1. Client assigns a color to an uncolored node
ClientAssign ==
    /\ clientReady
    /\ \E n \in Node : color[n] = NoColor
    /\ LET c == RandomColor IN
       /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, loopIter, loopSample, clientReady>>

\* 2. Loop process samples a set of peers and issues query messages
LoopSampleAction ==
    /\ \E lp \in SlushLoopProcess :
          /\ loopIter[lp] < SlushIterationCount
          /\ loopSample[lp] = {}
          /\ color[LoopNode[lp]] # NoColor
          /\ LET n == LoopNode[lp] IN
             LET peers == Node \ {n} IN
             /\ \E S \subseteq peers :
                    Cardinality(S) = SampleSetSize
                /\ let qps == { NodeQuery[p] : p \in S } in
                   /\ msgs' = msgs \cup
                        { [type |-> "query",
                           from |-> lp,
                           to   |-> qp,
                           color|-> color[n]] :
                           qp \in qps }
                /\ loopSample' = [loopSample EXCEPT ![lp] = S]
                /\ UNCHANGED <<color, loopIter, clientReady>>
    /\ UNCHANGED msgs

\* 3. Query process receives a query, possibly adopts the queried color,
\*    and replies with its current color
QueryRespond ==
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ \E qp \in SlushQueryProcess :
                /\ m.to = qp
                /\ LET n == QueryNode[qp] IN
                   /\ IF color[n] = NoColor
                         THEN color' = [color EXCEPT ![n] = m.color]
                         ELSE UNCHANGED color
                /\ msgs' = (msgs \ {m}) \cup
                           { [type |-> "reply",
                              from |-> qp,
                              to   |-> m.from,
                              color|-> (IF color[n] = NoColor THEN m.color ELSE color[n])]
                           }
                /\ UNCHANGED <<loopIter, loopSample, clientReady>>
    /\ UNCHANGED msgs

\* 4. Loop process collects all replies for its current sample,
\*    possibly flips its node's color, clears the sample and increments iteration
LoopTally ==
    /\ \E lp \in SlushLoopProcess :
          /\ loopSample[lp] # {}
          /\ LET S == loopSample[lp] IN
             /\ \A n \in S :
                  \E r \in msgs :
                     /\ r.type = "reply"
                     /\ r.to   = lp
                     /\ r.from = NodeQuery[n]
             /\ \* Count replies per color
                LET replies == { r \in msgs :
                                   r.type = "reply" /\ r.to = lp } IN
                LET redCount  == Cardinality({ r \in replies : r.color = "Red" }) IN
                LET blueCount == Cardinality({ r \in replies : r.color = "Blue" }) IN
                /\ IF redCount >= PickFlipThreshold
                      THEN color' = [color EXCEPT ![LoopNode[lp]] = "Red"]
                ELSE IF blueCount >= PickFlipThreshold
                      THEN color' = [color EXCEPT ![LoopNode[lp]] = "Blue"]
                ELSE UNCHANGED color
             /\ msgs' = msgs \ { r \in msgs :
                                   r.type = "reply" /\ r.to = lp }
             /\ loopIter' = [loopIter EXCEPT ![lp] = @ + 1]
             /\ loopSample' = [loopSample EXCEPT ![lp] = {}]
             /\ UNCHANGED clientReady
    /\ UNCHANGED msgs

\* 5. After completing all iterations, a loop process broadcasts a termination message
LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
          /\ loopIter[lp] = SlushIterationCount
          /\ \A qp \in SlushQueryProcess :
                /\ msgs' = msgs \cup
                      { [type |-> "term",
                         from |-> lp,
                         to   |-> qp,
                         color|-> NoColor] }
          /\ UNCHANGED <<color, loopIter, loopSample, clientReady>>
    /\ UNCHANGED msgs

\* 6. Query processes exit when they have received termination messages from all loops
QueryExit ==
    /\ \E qp \in SlushQueryProcess :
          /\ \A lp \in SlushLoopProcess :
                \E m \in msgs :
                   /\ m.type = "term"
                   /\ m.from = lp
                   /\ m.to   = qp
          /\ msgs' = msgs \ { m \in msgs :
                                m.type = "term" /\ m.to = qp }
          /\ UNCHANGED <<color, loopIter, loopSample, clientReady>>
    /\ UNCHANGED msgs

\* 7. Client becomes idle when every node has a color
ClientDone ==
    /\ \A n \in Node : color[n] # NoColor
    /\ clientReady' = FALSE
    /\ UNCHANGED <<color, msgs, loopIter, loopSample>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ LoopSampleAction
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryExit
    \/ ClientDone

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, loopIter, loopSample, clientReady>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
MessageSet == { m \in [type   : {"query","reply","term"},
                       from   : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
                       to     : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
                       color  : Colors] : TRUE }

TypeInvariant ==
    /\ color \in [Node -> Colors]
    /\ msgs \subseteq MessageSet
    /\ loopIter \in [SlushLoopProcess -> Nat]
    /\ loopSample \in [SlushLoopProcess -> SUBSET Node]

====