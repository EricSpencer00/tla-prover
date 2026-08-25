---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,                     \* Set of node identifiers
    SlushLoopProcess,         \* Set of loop process identifiers (one per node)
    SlushQueryProcess,        \* Set of query process identifiers (one per node)
    HostMapping,              \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,      \* Number of iterations each loop process must perform
    SampleSetSize,            \* Size of the peer sample taken each round
    PickFlipThreshold,        \* Minimum number of identical replies needed to flip
    NoColor,                  \* Symbol for the uncolored state
    NoMessage                 \* Symbol for the absence of a message

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Colors == {"Red", "Blue"}      \* the two possible colors

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : {"query", "reply", "term"},
            src  : Proc,
            dst  : Proc,
            col  : (Colors \cup {NoColor})]

\* ----------------------------------------------------------------------
\* Helper functions for the host mapping
\* ----------------------------------------------------------------------
NodeOfLoop(p) == 
    CHOOSE n \in Node : <<n, p, _>> \in HostMapping

NodeOfQuery(q) == 
    CHOOSE n \in Node : <<n, _, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,          \* [Node -> (Colors \cup {NoColor})]
    msgs,           \* SUBSET Message
    pc,             \* [Proc -> {"clientIdle", "clientAssign", "loopWaitColor",
                               "loopSample", "loopWaitReplies", "loopTerm",
                               "queryLoop"}]
    sampleSet,      \* [SlushLoopProcess -> SUBSET Node]  (peers sampled this round)
    iter,           \* [SlushLoopProcess -> Nat]        (iterations completed)
    replyCount      \* [SlushLoopProcess -> [c \in Colors |-> Nat]]  (tally)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in Proc |-> 
                IF p = "Client" THEN "clientIdle"
                ELSE IF p \in SlushLoopProcess THEN "loopWaitColor"
                ELSE "queryLoop"]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ iter = [p \in SlushLoopProcess |-> 0]
    /\ replyCount = [p \in SlushLoopProcess |-> [c \in Colors |-> 0]]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* --------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
\* --------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = "clientIdle"
    /\ \E n \in Node : color[n] = NoColor
    /\ LET n == CHOOSE n \in Node : color[n] = NoColor
           c == CHOOSE c \in Colors
       IN  /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pc, sampleSet, iter, replyCount>>
    /\ pc' = [pc EXCEPT !["Client"] = "clientIdle"]

\* --------------------------------------------------------------
\* 2. Loop process waits until its node is colored
\* --------------------------------------------------------------
LoopWaitColor(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "loopWaitColor"
    /\ color[NodeOfLoop(p)] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "loopSample"]
    /\ UNCHANGED <<color, msgs, sampleSet, iter, replyCount>>

\* --------------------------------------------------------------
\* 3. Loop process samples peers and sends query messages
\* --------------------------------------------------------------
LoopSample(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "loopSample"
    /\ iter[p] < SlushIterationCount
    /\ LET me == NodeOfLoop(p)
           peers == Node \ {me}
           sample == CHOOSE s \subseteq peers : Cardinality(s) = SampleSetSize
       IN  /\ sampleSet' = [sampleSet EXCEPT ![p] = sample]
    /\ msgs' = msgs \cup {
            [type |-> "query",
             src  |-> p,
             dst  |-> q,
             col  |-> color[me]]
            : q \in SlushQueryProcess :
                \E n \in Node : <<n, _, q>> \in HostMapping /\ n \in sampleSet'[p]
          }
    /\ pc' = [pc EXCEPT ![p] = "loopWaitReplies"]
    /\ UNCHANGED <<color, iter, replyCount>>

\* --------------------------------------------------------------
\* 4. Query process receives a query, possibly adopts the color,
\*    and replies
\* --------------------------------------------------------------
QueryReceive(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = "queryLoop"
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.dst = q
    /\ LET m == CHOOSE m \in msgs :
                m.type = "query" /\ m.dst = q
                n == NodeOfQuery(q)
                curCol == color[n]
                newCol == IF curCol = NoColor THEN m.col ELSE curCol
                colAfter == newCol
           IN  /\ color' = [color EXCEPT ![n] = colAfter]
    /\ msgs' = (msgs \ {m}) \cup {
            [type |-> "reply",
             src  |-> q,
             dst  |-> m.src,
             col  |-> color'[NodeOfQuery(q)]]
        }
    /\ UNCHANGED <<pc, sampleSet, iter, replyCount>>

\* --------------------------------------------------------------
\* 5. Loop process receives a reply and updates its tally
\* --------------------------------------------------------------
LoopReceiveReply(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "loopWaitReplies"
    /\ \E m \in msgs :
          /\ m.type = "reply"
          /\ m.dst = p
    /\ LET m == CHOOSE m \in msgs :
                m.type = "reply" /\ m.dst = p
                c == m.col
           IN  /\ replyCount' = [replyCount EXCEPT ![p][c] = @ + 1]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<color, sampleSet, iter, pc>>

\* --------------------------------------------------------------
\* 6. Loop process checks if all replies have arrived and possibly flips
\* --------------------------------------------------------------
LoopDecision(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "loopWaitReplies"
    /\ \A n \in sampleSet[p] :
          \E q \in SlushQueryProcess :
              <<n, _, q>> \in HostMapping /\ 
              \E m \in msgs : m.type = "reply" /\ m.dst = p /\ m.src = q
    /\ LET curNode == NodeOfLoop(p)
           curCol   == color[curNode]
           cntRed   == replyCount[p]["Red"]
           cntBlue  == replyCount[p]["Blue"]
           newCol   == 
                IF cntRed >= PickFlipThreshold THEN "Red"
                ELSE IF cntBlue >= PickFlipThreshold THEN "Blue"
                ELSE curCol
           iter'    == [iter EXCEPT ![p] = @ + 1]
           sampleSet' == [sampleSet EXCEPT ![p] = {}]
           replyCount' == [replyCount EXCEPT ![p] = [c \in Colors |-> 0]]
           pc'      == 
                IF iter'[p] = SlushIterationCount 
                THEN [pc EXCEPT ![p] = "loopTerm"]
                ELSE [pc EXCEPT ![p] = "loopSample"]
       IN  /\ color' = [color EXCEPT ![curNode] = newCol]
           /\ UNCHANGED msgs
           /\ sampleSet = sampleSet'   \* (already set above)
           /\ iter = iter'
           /\ replyCount = replyCount'
           /\ pc = pc'

\* --------------------------------------------------------------
\* 7. Loop process terminates and broadcasts a termination message
\* --------------------------------------------------------------
LoopTerminate(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "loopTerm"
    /\ msgs' = msgs \cup {
            [type |-> "term",
             src  |-> p,
             dst  |-> q,
             col  |-> NoColor] : q \in SlushQueryProcess
        }
    /\ pc' = [pc EXCEPT ![p] = "clientIdle"]   \* loop process done
    /\ UNCHANGED <<color, sampleSet, iter, replyCount>>

\* --------------------------------------------------------------
\* 8. Query processes exit when all termination messages have been received
\* --------------------------------------------------------------
QueryExit(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = "queryLoop"
    /\ \A p \in SlushLoopProcess :
          \E m \in msgs : m.type = "term" /\ m.dst = q /\ m.src = p
    /\ pc' = [pc EXCEPT ![q] = "clientIdle"]
    /\ msgs' = msgs \ { m \in msgs : m.type = "term" /\ m.dst = q }
    /\ UNCHANGED <<color, sampleSet, iter, replyCount>>

\* --------------------------------------------------------------
\* Next-state relation
\* --------------------------------------------------------------
Next ==
    \/ \E p \in SlushLoopProcess : LoopWaitColor(p)
    \/ \E p \in SlushLoopProcess : LoopSample(p)
    \/ \E q \in SlushQueryProcess   : QueryReceive(q)
    \/ \E p \in SlushLoopProcess : LoopReceiveReply(p)
    \/ \E p \in SlushLoopProcess : LoopDecision(p)
    \/ \E p \in SlushLoopProcess : LoopTerminate(p)
    \/ \E q \in SlushQueryProcess   : QueryExit(q)
    \/ ClientAssign

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sampleSet, iter, replyCount>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ \A n \in Node : color[n] \in Colors \cup {NoColor}
    /\ \A m \in msgs :
          /\ m.type \in {"query","reply","term"}
          /\ m.src \in Proc
          /\ m.dst \in Proc
          /\ m.col \in Colors \cup {NoColor}

\* ----------------------------------------------------------------------
\* Theorems (optional)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====