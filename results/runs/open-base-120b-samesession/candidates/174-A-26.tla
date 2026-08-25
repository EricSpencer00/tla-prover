---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers
    SlushQueryProcess,  \* Set of query process identifiers
    HostMapping,        \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,\* Number of iterations each loop process performs
    SampleSetSize,      \* Number of peers sampled each round
    PickFlipThreshold,  \* Threshold for adopting a color
    NoColor,            \* Value representing an uncolored node
    NoMessage           \* Placeholder value for messages (not used directly)

\* ----------------------------------------------------------------------
\* Colors used by the protocol (two possible opinions)
ColorSet == {"Red", "Blue"}

\* Message record type
Message ==
    [ type : {"query", "reply", "term"},
      src  : (SlushLoopProcess \cup SlushQueryProcess),
      dst  : Node,
      col  : (NoColor \cup ColorSet) ]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    color,      \* [node -> (NoColor \cup ColorSet)]
    msgs,       \* Set of messages in transit
    sampleSet,  \* [loopProc -> SUBSET Node]  (current sample of peers)
    iter        \* [loopProc -> Nat]          (iterations performed)

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ color     = [n \in Node |-> NoColor]
    /\ msgs      = {}
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iter      = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Action: client assigns a random color to an uncolored node
ClientAssign ==
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ \E c \in ColorSet :
                /\ color' = [color EXCEPT ![n] = c]
                /\ UNCHANGED <<msgs, sampleSet, iter>>

\* ----------------------------------------------------------------------
\* Action: a loop process samples peers and sends query messages
LoopSendQuery ==
    /\ \E t \in HostMapping :
          LET n  == t[1]
              lp == t[2] IN
          /\ iter[lp] < SlushIterationCount
          /\ color[n] # NoColor
          /\ sampleSet[lp] = {}
          /\ \E S \subseteq Node \ {n} :
                /\ Cardinality(S) = SampleSetSize
                /\ sampleSet' = [sampleSet EXCEPT ![lp] = S]
                /\ msgs'      = msgs \cup
                                 { [type |-> "query",
                                    src  |-> lp,
                                    dst  |-> m,
                                    col  |-> color[n]] : m \in S }
                /\ UNCHANGED <<color, iter>>

\* ----------------------------------------------------------------------
\* Action: a query process receives a query, possibly adopts the color,
\* and replies
QueryRespond ==
    /\ \E qMsg \in msgs :
          /\ qMsg.type = "query"
          LET n     == qMsg.dst
              lpSrc == qMsg.src
              colQ   == qMsg.col IN
          /\ \E t \in HostMapping :
                /\ t[1] = n
                LET qp == t[3] IN
                /\ IF color[n] = NoColor
                      THEN color' = [color EXCEPT ![n] = colQ]
                      ELSE color' = color
                /\ msgs' = (msgs \ {qMsg}) \cup
                           { [type |-> "reply",
                              src  |-> qp,
                              dst  |-> lpSrc,
                              col  |-> color'[n]] }
                /\ UNCHANGED <<sampleSet, iter>>
    /\ UNCHANGED <<sampleSet, iter>>

\* ----------------------------------------------------------------------
\* Action: a loop process tallies replies and possibly flips its color
LoopTally ==
    /\ \E t \in HostMapping :
          LET n  == t[1]
              lp == t[2] IN
          /\ sampleSet[lp] # {}
          /\ \A n2 \in sampleSet[lp] :
                \E r \in msgs :
                     /\ r.type = "reply"
                     /\ r.dst  = lp
                     /\ (\E tt \in HostMapping :
                          tt[1] = n2 /\ tt[3] = r.src)
          LET replies == { r \in msgs : r.type = "reply" /\ r.dst = lp } IN
          LET redCnt  == Cardinality({ r \in replies : r.col = "Red" }) IN
          LET blueCnt == Cardinality({ r \in replies : r.col = "Blue" }) IN
          LET newCol ==
                IF redCnt  >= PickFlipThreshold THEN "Red"
                ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                ELSE color[n] 
          IN
          /\ color'     = [color EXCEPT ![n] = newCol]
          /\ iter'      = [iter EXCEPT ![lp] = iter[lp] + 1]
          /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
          /\ msgs'      = msgs \ replies
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: a loop process that has completed all iterations (termination)
LoopTerminate ==
    /\ \E t \in HostMapping :
          LET lp == t[2] IN
          /\ iter[lp] = SlushIterationCount
          /\ UNCHANGED <<color, msgs, sampleSet, iter>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ ClientAssign
    \/ LoopSendQuery
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ color \in [Node -> (NoColor \cup ColorSet)]
    /\ msgs  \subseteq Message
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iter  \in [SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<color, msgs, sampleSet, iter>>

=============================================================================