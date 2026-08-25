---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Node,               \* set of all node identifiers
    SlushLoopProcess,   \* set of loop process identifiers (one per node)
    SlushQueryProcess,  \* set of query process identifiers (one per node)
    HostMapping,        \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,\* maximum number of iterations each loop performs
    SampleSetSize,      \* number of peers sampled each round
    PickFlipThreshold,  \* threshold to adopt a color
    NoColor,            \* special value meaning "uncolored"
    NoMessage           \* special placeholder for "no message"

\* ----------------------------------------------------------------------
\* Colors used by the protocol (two concrete colors)
\* These need not be declared as constants in the .cfg; they are internal.
\* ----------------------------------------------------------------------
CONSTANTS ColorA, ColorB
ASSUME ColorSet == {ColorA, ColorB}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    color,          \* [node \in Node |-> ColorA | ColorB | NoColor]
    msgs,           \* set of in‑flight messages
    sampleSet,      \* [loopProc \in SlushLoopProcess |-> SUBSET SlushQueryProcess]
    iterCnt         \* [loopProc \in SlushLoopProcess |-> Nat]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
HostNode(p) ==
    IF p \in SlushLoopProcess THEN
        CHOOSE n \in Node :
            \E q \in SlushQueryProcess :
                <<n, p, q>> \in HostMapping
    ELSE IF p \in SlushQueryProcess THEN
        CHOOSE n \in Node :
            \E l \in SlushLoopProcess :
                <<n, l, p>> \in HostMapping
    ELSE NoNode

QueryMsg(src, dst, col) == [type |-> "query", src |-> src, dst |-> dst, col |-> col]
ReplyMsg(src, dst, col) == [type |-> "reply", src |-> src, dst |-> dst, col |-> col]
TermMsg(src)           == [type |-> "term",  src |-> src]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ iterCnt = [p \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ \E n \in Node : color[n] = NoColor
    /\ LET chosen == CHOOSE n \in Node : color[n] = NoColor
       IN
          /\ col \in ColorSet
          /\ color' = [color EXCEPT ![chosen] = col]
    /\ UNCHANGED <<msgs, sampleSet, iterCnt>>

LoopStart(p) ==
    /\ p \in SlushLoopProcess
    /\ color[HostNode(p)] # NoColor
    /\ UNCHANGED <<color, msgs, sampleSet, iterCnt>>

LoopQuery(p) ==
    /\ p \in SlushLoopProcess
    /\ iterCnt[p] < SlushIterationCount
    /\ sampleSet[p] = {}                     \* not already sampling
    /\ LET others == { q \in SlushQueryProcess :
                         q # HostQuery(p) }
       IN
          /\ sample == CHOOSE S \subseteq others :
                         Cardinality(S) = SampleSetSize
          /\ sampleSet' = [sampleSet EXCEPT ![p] = sample]
          /\ msgs' = msgs \cup
                     { QueryMsg(p, q, color[HostNode(p)]) : q \in sample }
    /\ UNCHANGED <<color, iterCnt>>

HostQuery(p) ==
    CHOOSE q \in SlushQueryProcess :
        <<HostNode(p), p, q>> \in HostMapping

QueryRespond ==
    /\ \E m \in msgs : m.type = "query"
    /\ LET m == CHOOSE m \in msgs : m.type = "query"
       IN
          /\ q == m.dst
          /\ n == HostNode(q)
          /\ col == m.col
          /\ IF color[n] = NoColor
                THEN color' = [color EXCEPT ![n] = col]
                ELSE color' = color
          /\ msgs' = (msgs \ {m}) \cup
                     { ReplyMsg(q, m.src, color'[n]) }
    /\ UNCHANGED <<sampleSet, iterCnt>>

LoopTally(p) ==
    /\ p \in SlushLoopProcess
    /\ sampleSet[p] # {}                     \* a sample exists
    /\ \A q \in sampleSet[p] :
          \E r \in msgs :
                /\ r.type = "reply"
                /\ r.dst = p
                /\ r.src = q
    /\ LET replies == { r \in msgs :
                         r.type = "reply" /\ r.dst = p /\ r.src \in sampleSet[p] }
       IN
          /\ reds  == Cardinality({ r \in replies : r.col = ColorA })
          /\ blues == Cardinality({ r \in replies : r.col = ColorB })
          /\ newCol ==
               IF reds  >= PickFlipThreshold THEN ColorA
               ELSE IF blues >= PickFlipThreshold THEN ColorB
               ELSE color[HostNode(p)]
          /\ color' = [color EXCEPT ![HostNode(p)] = newCol]
          /\ msgs' = msgs \ replies
          /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
          /\ iterCnt' = [iterCnt EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<>>

LoopTerminate(p) ==
    /\ p \in SlushLoopProcess
    /\ iterCnt[p] = SlushIterationCount
    /\ msgs' = msgs \cup { TermMsg(p) }
    /\ UNCHANGED <<color, sampleSet, iterCnt>>

QueryExit ==
    /\ \A p \in SlushLoopProcess : TermMsg(p) \in msgs
    /\ UNCHANGED <<color, msgs, sampleSet, iterCnt>>

Next ==
    \/ \E p \in SlushLoopProcess : LoopStart(p)
    \/ \E p \in SlushLoopProcess : LoopQuery(p)
    \/ QueryRespond
    \/ \E p \in SlushLoopProcess : LoopTally(p)
    \/ \E p \in SlushLoopProcess : LoopTerminate(p)
    \/ QueryExit
    \/ ClientAssign

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sampleSet, iterCnt>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (ColorSet \cup {NoColor})]
    /\ msgs \subseteq
         { m \in [type : {"query","reply","term"}] :
               \/ /\ m.type = "query"
                  /\ m.src \in SlushLoopProcess
                  /\ m.dst \in SlushQueryProcess
                  /\ m.col \in (ColorSet \cup {NoColor})
               \/ /\ m.type = "reply"
                  /\ m.src \in SlushQueryProcess
                  /\ m.dst \in SlushLoopProcess
                  /\ m.col \in (ColorSet \cup {NoColor})
               \/ /\ m.type = "term"
                  /\ m.src \in SlushLoopProcess }
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterCnt \in [SlushLoopProcess -> Nat]

====