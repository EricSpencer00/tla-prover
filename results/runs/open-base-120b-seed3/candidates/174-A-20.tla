---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* --------------------------------------------------------------
\* CONSTANTS (to be instantiated by the .cfg file)
\* --------------------------------------------------------------
CONSTANTS 
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Size of the random peer sample per iteration
    PickFlipThreshold,  \* Threshold for adopting a color
    NoColor,            \* Special value meaning “uncolored”
    NoMessage           \* Special value not belonging to the Message set

\* --------------------------------------------------------------
\* Derived sets and helper functions
\* --------------------------------------------------------------
\* The two possible colors (chosen arbitrarily)
ColorSet == {"Red", "Blue"}

\* Mapping from a node to its associated loop process
LoopOf(node) == 
    IF \E l \in SlushLoopProcess : <<node, l, q>> \in HostMapping 
    THEN CHOOSE l \in SlushLoopProcess : <<node, l, q>> \in HostMapping
    ELSE NoMessage

\* Mapping from a node to its associated query process
QueryOf(node) == 
    IF \E q \in SlushQueryProcess : <<node, l, q>> \in HostMapping 
    THEN CHOOSE q \in SlushQueryProcess : <<node, l, q>> \in HostMapping
    ELSE NoMessage

\* The set of all processes (loop, query and a distinguished client)
AllProc == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

\* --------------------------------------------------------------
\* Message definition
\* --------------------------------------------------------------
Message == [type   : {"query", "reply", "term"},
            src    : AllProc,
            dst    : AllProc,
            color  : ColorSet \cup {NoColor}]

\* --------------------------------------------------------------
\* Variables
\* --------------------------------------------------------------
VARIABLES 
    colors,   \* [Node -> (ColorSet \cup {NoColor})]   current color of each node
    msgs,     \* SUBSET of Message, the in‑flight messages
    pc,       \* [AllProc -> {"ready", "wait", "sample", "awaitReplies", 
                           "terminate", "done", "replyLoop"}]   program counters
    sample,   \* [SlushLoopProcess -> SUBSET Node]   peers sampled this round
    iter      \* [SlushLoopProcess -> Nat]           number of completed iterations

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc     = [p \in AllProc |
                    IF p = "Client"               THEN "ready"
                    ELSE IF p \in SlushLoopProcess THEN "wait"
                    ELSE                               "replyLoop"]
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ iter   = [l \in SlushLoopProcess |-> 0]

\* --------------------------------------------------------------
\* Actions
\* --------------------------------------------------------------

\* (1) Client assigns a random color to an uncolored node
ClientAssign ==
    /\ pc["Client"] = "ready"
    /\ \E n \in Node :
          /\ colors[n] = NoColor
          /\ c \in ColorSet
          /\ colors' = [colors EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pc, sample, iter>>
    /\ pc' = [pc EXCEPT !["Client"] = "ready"]  \* client stays ready

\* (2) Loop process waits until its host node gets a color
LoopRequireColor(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "wait"
    /\ LET n == CHOOSE n \in Node : LoopOf(n) = l IN
          colors[n] # NoColor
    /\ pc' = [pc EXCEPT ![l] = "sample"]
    /\ UNCHANGED <<colors, msgs, sample, iter>>

\* (3) Loop process selects a random sample and sends queries
LoopSample(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "sample"
    /\ LET n == CHOOSE n \in Node : LoopOf(n) = l IN
       \* Choose a subset of other nodes of the required size
       \E s \in SUBSET (Node \ {n}) :
            /\ Cardinality(s) = SampleSetSize
            /\ sample' = [sample EXCEPT ![l] = s]
            /\ msgs' = msgs \cup 
               { [type  |-> "query",
                  src   |-> l,
                  dst   |-> QueryOf(p),
                  color |-> colors[n]] : p \in s }
    /\ pc' = [pc EXCEPT ![l] = "awaitReplies"]
    /\ UNCHANGED <<colors, iter>>

\* (4) Query process responds to a query (and possibly adopts the queried color)
QueryRespond(q) ==
    /\ q \in SlushQueryProcess
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.dst = q
          /\ LET n == CHOOSE n \in Node : QueryOf(n) = q IN
               /\ colors' = 
                    IF colors[n] = NoColor
                    THEN [colors EXCEPT ![n] = m.color]
                    ELSE colors
               /\ reply == [type  |-> "reply",
                            src   |-> q,
                            dst   |-> m.src,
                            color |-> colors'[n]]
          /\ msgs' = (msgs \ {m}) \cup {reply}
    /\ UNCHANGED <<pc, sample, iter>>

\* (5) Loop process tallies replies and possibly flips its color
LoopTally(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "awaitReplies"
    /\ LET n == CHOOSE n \in Node : LoopOf(n) = l IN
       s == sample[l]
    /\ \A p \in s :
          \E r \in msgs :
               /\ r.type = "reply"
               /\ r.dst = l
               /\ r.src = QueryOf(p)
    /\ \* Count how many replies carry each color
       reds   == Cardinality({ r \in msgs : 
                               r.type = "reply" /\ r.dst = l /\ r.color = "Red" })
       blues  == Cardinality({ r \in msgs : 
                               r.type = "reply" /\ r.dst = l /\ r.color = "Blue" })
    /\ newColor == 
          IF reds >= PickFlipThreshold THEN "Red"
          ELSE IF blues >= PickFlipThreshold THEN "Blue"
          ELSE colors[n]
    /\ colors' = [colors EXCEPT ![n] = newColor]
    /\ iter'   = [iter EXCEPT ![l] = @ + 1]
    /\ sample' = [sample EXCEPT ![l] = {}]
    /\ msgs'   = msgs \ 
                { r \in msgs : r.type = "reply" /\ r.dst = l }
    /\ pc' = 
        IF iter'[l] >= SlushIterationCount
        THEN [pc EXCEPT ![l] = "terminate"]
        ELSE [pc EXCEPT ![l] = "sample"]
    /\ UNCHANGED <<pc, sample, iter>>  \* (pc, sample, iter already updated)

\* (6) Loop process terminates (broadcasts a termination message)
LoopTerminate(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "terminate"
    /\ msgs' = msgs \cup { [type |-> "term", src |-> l, dst |-> "All", color |-> NoColor] }
    /\ pc' = [pc EXCEPT ![l] = "done"]
    /\ UNCHANGED <<colors, sample, iter>>

\* (7) Query processes exit when all loop processes are done
QueryExit(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = "replyLoop"
    /\ \A l \in SlushLoopProcess : pc[l] = "done"
    /\ pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<colors, msgs, sample, iter>>

\* --------------------------------------------------------------
\* Next-state relation (disjunction of all possible actions)
\* --------------------------------------------------------------
Next ==
    \/ \E l \in SlushLoopProcess : LoopRequireColor(l)
    \/ \E l \in SlushLoopProcess : LoopSample(l)
    \/ \E q \in SlushQueryProcess : QueryRespond(q)
    \/ \E l \in SlushLoopProcess : LoopTally(l)
    \/ \E l \in SlushLoopProcess : LoopTerminate(l)
    \/ \E q \in SlushQueryProcess : QueryExit(q)
    \/ ClientAssign

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, pc, sample, iter>>

\* --------------------------------------------------------------
\* Type invariant (required)
\* --------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> (ColorSet \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ pc \in [AllProc -> {"ready","wait","sample","awaitReplies",
                          "terminate","done","replyLoop"}]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]

\* --------------------------------------------------------------
\* Liveness (termination) – not required by the .cfg but useful
\* --------------------------------------------------------------
Termination == <>[]( \A p \in AllProc : pc[p] = "done")

====