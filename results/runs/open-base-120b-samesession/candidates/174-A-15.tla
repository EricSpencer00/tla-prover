---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers (one per node)
    SlushQueryProcess,   \* Set of query process identifiers (one per node)
    HostMapping,         \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* Number of iterations each loop process performs
    SampleSetSize,       \* Size of the peer sample taken each round
    PickFlipThreshold,   \* Minimum number of identical replies needed to flip
    NoColor,             \* Sentinel for an uncolored node
    NoMessage             \* Sentinel for the absence of a message

\* ----------------------------------------------------------------------
\* Derived sets and helper functions
\* ----------------------------------------------------------------------
ColorSet == {"Red", "Blue"}

\* Mapping from a loop process to its host node
HostNode(lp) == 
    CHOOSE n \in Node : <<n, lp, q>> \in HostMapping

\* Mapping from a loop process to its query process
HostQuery(lp) ==
    CHOOSE q \in SlushQueryProcess : <<HostNode(lp), lp, q>> \in HostMapping

\* Mapping from a query process to its host node
HostNodeFromQuery(qp) ==
    CHOOSE n \in Node : \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,      \* [node -> ColorSet \/ {NoColor}]
    msgs,       \* Set of in‑flight messages
    pc,         \* [proc -> PCState]  (process program counters)
    sample,     \* [loopProc -> SUBSET SlushQueryProcess]  (current sample)
    iter        \* [loopProc -> Nat]   (iterations completed)

\* PC states for loop processes
LoopPC == {"waitColor", "sample", "awaitReplies", "done", "finished"}

\* PC states for query processes
QueryPC == {"run", "done"}

\* The set of all processes that have a program counter entry
AllProcs == SlushLoopProcess \cup SlushQueryProcess

\* Message record shape
Message ==
    [type   : {"query", "reply", "term"},
     src    : (SlushLoopProcess \cup SlushQueryProcess),
     dst    : (SlushLoopProcess \cup SlushQueryProcess),
     color  : (ColorSet \cup {NoColor})]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in AllProcs |
                IF p \in SlushLoopProcess
                THEN "waitColor"
                ELSE "run"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
AssignColor ==
    \E n \in Node :
        /\ color[n] = NoColor
        /\ \E c \in ColorSet :
            /\ color' = [color EXCEPT ![n] = c]
            /\ UNCHANGED <<msgs, pc, sample, iter>>

\* 2. Loop process waits until its host node is colored
RequireColor ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "waitColor"
        /\ color[HostNode(lp)] # NoColor
        /\ pc' = [pc EXCEPT ![lp] = "sample"]
        /\ UNCHANGED <<color, msgs, sample, iter>>

\* 3. Loop process samples peers and sends query messages
SamplePeers ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "sample"
        /\ LET others == SlushQueryProcess \ {HostQuery(lp)} IN
           \E s \in SUBSET others :
               Cardinality(s) = SampleSetSize
        IN
        /\ sample' = [sample EXCEPT ![lp] = s]
        /\ pc' = [pc EXCEPT ![lp] = "awaitReplies"]
        /\ msgs' = msgs \cup
           { [type |-> "query",
              src  |-> lp,
              dst  |-> q,
              color|-> color[HostNode(lp)]] : q \in s }
        /\ UNCHANGED <<color, iter>>

\* 4. Query process responds to a query (adopting color if uncolored)
RespondToQuery ==
    \E qp \in SlushQueryProcess, m \in msgs :
        /\ m.type = "query"
        /\ m.dst = qp
        /\ LET n == HostNodeFromQuery(qp) IN
           /\ IF color[n] = NoColor
              THEN color' = [color EXCEPT ![n] = m.color]
              ELSE color' = color
        /\ LET reply == [type |-> "reply",
                         src  |-> qp,
                         dst  |-> m.src,
                         color|-> color'[n]] IN
           msgs' = (msgs \ {m}) \cup {reply}
        /\ UNCHANGED <<pc, sample, iter>>

\* 5. Loop process tallies replies and possibly flips its node's color
TallyReplies ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "awaitReplies"
        /\ LET s == sample[lp] IN
           /\ s # {}
           /\ \A q \in s :
                \E r \in msgs :
                    /\ r.type = "reply"
                    /\ r.src = q
                    /\ r.dst = lp
        /\ LET redCnt  == Cardinality({ r \in msgs :
                                        r.type = "reply" /\ r.dst = lp /\ r.color = "Red"}),
               blueCnt == Cardinality({ r \in msgs :
                                        r.type = "reply" /\ r.dst = lp /\ r.color = "Blue"}),
               curNode == HostNode(lp),
               curCol  == color[curNode],
               newCol  == IF redCnt >= PickFlipThreshold THEN "Red"
                         ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                         ELSE curCol
           IN
           /\ color' = [color EXCEPT ![curNode] = newCol]
           /\ sample' = [sample EXCEPT ![lp] = {}]
           /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
           /\ pc' = [pc EXCEPT ![lp] =
                     IF iter'[lp] < SlushIterationCount
                     THEN "sample"
                     ELSE "done"]
           /\ UNCHANGED msgs

\* 6. Loop process broadcasts termination messages after finishing iterations
SendTermination ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "done"
        /\ msgs' = msgs \cup
           { [type |-> "term",
              src  |-> lp,
              dst  |-> qp,
              color|-> NoColor] : qp \in SlushQueryProcess }
        /\ pc' = [pc EXCEPT ![lp] = "finished"]
        /\ UNCHANGED <<color, sample, iter>>

\* 7. Query processes exit when they have received termination from all loop processes
QueryExit ==
    \E qp \in SlushQueryProcess :
        /\ pc[qp] = "run"
        /\ \A lp \in SlushLoopProcess :
              \E m \in msgs :
                 /\ m.type = "term"
                 /\ m.src = lp
                 /\ m.dst = qp
        /\ pc' = [pc EXCEPT ![qp] = "done"]
        /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ AssignColor
    \/ RequireColor
    \/ SamplePeers
    \/ RespondToQuery
    \/ TallyReplies
    \/ SendTermination
    \/ QueryExit

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
MessageSet ==
    { m \in Message :
        IF m.type = "query"   THEN m.color \in ColorSet
        ELSE IF m.type = "reply" THEN m.color \in ColorSet
        ELSE                         m.color = NoColor }

TypeInvariant ==
    /\ color \in [Node -> (ColorSet \cup {NoColor})]
    /\ msgs \subseteq MessageSet
    /\ pc \in [AllProcs -> (LoopPC \cup QueryPC)]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iter \in [SlushLoopProcess -> Nat]

=============================================================================