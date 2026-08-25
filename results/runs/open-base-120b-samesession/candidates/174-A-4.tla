---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  CONSTANTS (provided by the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Node,                 \* Set of node identifiers
    SlushLoopProcess,     \* Set of loop process identifiers
    SlushQueryProcess,    \* Set of query process identifiers
    HostMapping,          \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,  \* Number of iterations each loop process performs
    SampleSetSize,        \* Size of the sampling set per iteration
    PickFlipThreshold,    \* Threshold for flipping colors
    NoColor,              \* Special value meaning “uncolored”
    NoMessage             \* Special payload for termination messages

(*--------------------------------------------------------------------
  Derived sets and helper functions
--------------------------------------------------------------------*)
Colors == {"Red", "Blue"}

Message == [type    : {"query", "reply", "term"},
            from    : (SlushLoopProcess \cup SlushQueryProcess),
            to      : (SlushLoopProcess \cup SlushQueryProcess),
            payload : (Colors \cup {NoColor, NoMessage})]

\* Mapping from a node to the loop process that runs on it
LoopProcOfNode(n) ==
    CHOOSE l \in SlushLoopProcess :
        \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

\* Mapping from a node to the query process that runs on it
QueryProcOfNode(n) ==
    CHOOSE q \in SlushQueryProcess :
        \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\* The node that hosts a given loop process
HostNodeOfLoop(l) ==
    CHOOSE n \in Node :
        <<n, l, QueryProcOfNode(n)>> \in HostMapping

\* The node that hosts a given query process
HostNodeOfQuery(q) ==
    CHOOSE n \in Node :
        <<n, LoopProcOfNode(n), q>> \in HostMapping

(*--------------------------------------------------------------------
  VARIABLES
--------------------------------------------------------------------*)
VARIABLES
    color,        \* [Node -> (Colors \cup {NoColor})]
    msgs,         \* Subset of Message
    pc,           \* [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> Nat ]
    sampleSet,    \* [SlushLoopProcess -> SUBSET Node]
    iterCnt       \* [SlushLoopProcess -> Nat]

vars == <<color, msgs, pc, sampleSet, iterCnt>>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 0]
    /\ sampleSet = [l \in SlushLoopProcess |-> {}]
    /\ iterCnt = [l \in SlushLoopProcess |-> 0]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

\* ------------------------------------------------------------------
\* Client assigns a random color to an uncolored node
\* ------------------------------------------------------------------
ClientAssign ==
    /\ \E n \in Node : color[n] = NoColor
    /\ LET c == CHOOSE col \in Colors : TRUE
       IN color' = [color EXCEPT ![n] = c]
    /\ pc' = [pc EXCEPT !["Client"] = pc["Client"] + 1]
    /\ UNCHANGED <<msgs, sampleSet, iterCnt>>

\* ------------------------------------------------------------------
\* Loop process waits until its host node has been colored
\* ------------------------------------------------------------------
LoopWaitColor(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 0
    /\ color[HostNodeOfLoop(l)] # NoColor
    /\ pc' = [pc EXCEPT ![l] = 1]
    /\ UNCHANGED <<color, msgs, sampleSet, iterCnt>>

\* ------------------------------------------------------------------
\* Loop process selects a random sample and sends queries
\* ------------------------------------------------------------------
LoopSample(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 1
    /\ LET otherNodes == Node \ {HostNodeOfLoop(l)} IN
       CHOOSE S \in SUBSET otherNodes :
           Cardinality(S) = SampleSetSize
       IN
          sampleSet' = [sampleSet EXCEPT ![l] = S]
    /\ LET qMsgs == { [type    |-> "query",
                       from    |-> l,
                       to      |-> QueryProcOfNode(n),
                       payload |-> color[HostNodeOfLoop(l)] ] :
                       n \in sampleSet' [l] }
       IN msgs' = msgs \cup qMsgs
    /\ pc' = [pc EXCEPT ![l] = 2]
    /\ UNCHANGED <<color, iterCnt>>

\* ------------------------------------------------------------------
\* Query process replies to a received query (adopting color if needed)
\* ------------------------------------------------------------------
QueryReply(q) ==
    /\ q \in SlushQueryProcess
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.to   = q
    /\ LET m == CHOOSE mm \in msgs :
                 mm.type = "query" /\ mm.to = q
         hostNode == HostNodeOfQuery(q)
         adoptColor == IF color[hostNode] = NoColor THEN m.payload ELSE color[hostNode]
         replyMsg  == [type    |-> "reply",
                       from    |-> q,
                       to      |-> m.from,
                       payload |-> adoptColor]
       IN /\ color' = [color EXCEPT ![hostNode] = adoptColor]
          /\ msgs' = (msgs \ {m}) \cup {replyMsg}
    /\ UNCHANGED <<pc, sampleSet, iterCnt>>

\* ------------------------------------------------------------------
\* Loop process tallies replies, possibly flips its node's color,
\* increments iteration counter and may terminate
\* ------------------------------------------------------------------
LoopTally(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 2
    /\ \A m \in msgs : ~(m.type = "query" /\ m.from = l)   \* all queries answered
    /\ LET replies == { m \in msgs : m.type = "reply" /\ m.to = l } IN
       LET cnt(c) == Cardinality({ r \in replies : r.payload = c }) IN
       LET newCol ==
            IF cnt("Red") >= PickFlipThreshold THEN "Red"
            ELSE IF cnt("Blue") >= PickFlipThreshold THEN "Blue"
            ELSE color[HostNodeOfLoop(l)]
       IN
          color' = [color EXCEPT ![HostNodeOfLoop(l)] = newCol]
    /\ msgsNoReplies = msgs \ replies
    /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
    /\ iterCnt' = [iterCnt EXCEPT ![l] = iterCnt[l] + 1]
    /\ IF iterCnt[l] + 1 = SlushIterationCount THEN
           /\ LET termMsgs == { [type    |-> "term",
                                 from    |-> l,
                                 to      |-> q,
                                 payload |-> NoMessage] :
                                 q \in SlushQueryProcess }
              IN msgs' = msgsNoReplies \cup termMsgs
           /\ pc' = [pc EXCEPT ![l] = 3]   \* termination state for this loop process
       ELSE
           /\ msgs' = msgsNoReplies
           /\ pc' = [pc EXCEPT ![l] = 1]   \* start next iteration

\* ------------------------------------------------------------------
\* Query process consumes a termination message; when all term messages
\* have been received it moves to a final “done” state (pc = 4)
\* ------------------------------------------------------------------
QueryTerminate(q) ==
    /\ q \in SlushQueryProcess
    /\ \E m \in msgs :
          /\ m.type = "term"
          /\ m.to   = q
    /\ LET m == CHOOSE mm \in msgs :
                 mm.type = "term" /\ mm.to = q
       IN msgs' = msgs \ {m}
    /\ IF \A l \in SlushLoopProcess :
           \A t \in msgs : ~(t.type = "term" /\ t.from = l)
       THEN pc' = [pc EXCEPT ![q] = 4]    \* done
       ELSE pc' = pc
    /\ UNCHANGED <<color, sampleSet, iterCnt>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ ClientAssign
    \/ \E l \in SlushLoopProcess : LoopWaitColor(l)
    \/ \E l \in SlushLoopProcess : LoopSample(l)
    \/ \E q \in SlushQueryProcess : QueryReply(q)
    \/ \E l \in SlushLoopProcess : LoopTally(l)
    \/ \E q \in SlushQueryProcess : QueryTerminate(q)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> Nat ]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCnt \in [SlushLoopProcess -> Nat]

====