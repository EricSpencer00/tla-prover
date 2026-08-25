---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,                \* the set of nodes
    SlushLoopProcess,    \* one loop process per node
    SlushQueryProcess,   \* one query process per node
    HostMapping,         \* set of triples <<node, loop, query>>
    SlushIterationCount, \* number of iterations each loop executes
    SampleSetSize,       \* size of the sample drawn each round
    PickFlipThreshold,   \* threshold needed to flip colour
    NoColor,             \* special value meaning “uncoloured”
    NoMessage            \* special value meaning “no message”

\* ----------------------------------------------------------------------
\* Colours used by the protocol
Colors == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\* Helper functions mapping processes ↔ nodes via HostMapping
NodeOfLoop(l) == 
    CHOOSE n \in Node : <<n, l, q>> \in HostMapping

NodeOfQuery(q) == 
    CHOOSE n \in Node : <<n, l, q>> \in HostMapping

LoopOfNode(n) == 
    CHOOSE l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

QueryOfNode(n) == 
    CHOOSE q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* Message definition
Message ==
    [type   : {"query", "reply", "term"},
     src    : (SlushLoopProcess \cup SlushQueryProcess),
     dst    : (SlushLoopProcess \cup SlushQueryProcess),
     colour : Colors \cup {NoColor}]

\* ----------------------------------------------------------------------
VARIABLES
    colour,      \* [Node -> (Colors \cup {NoColor})]
    msgs,        \* set of messages in flight
    pcLoop,      \* [SlushLoopProcess -> {"wait","sample","tally","done"}]
    pcQuery,     \* [SlushQueryProcess -> {"reply","done"}]
    sample,      \* [SlushLoopProcess -> SUBSET Node]   (peers sampled this round)
    iter         \* [SlushLoopProcess -> Nat]          (iterations completed)

vars == <<colour, msgs, pcLoop, pcQuery, sample, iter>>

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ colour = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pcLoop = [p \in SlushLoopProcess |-> "wait"]
    /\ pcQuery= [q \in SlushQueryProcess |-> "reply"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Action: client assigns a colour to an uncoloured node
ClientAssign ==
    /\ \E n \in Node :
          /\ colour[n] = NoColor
          /\ c \in Colors
          /\ colour' = [colour EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pcLoop, pcQuery, sample, iter>>

\* ----------------------------------------------------------------------
\* Action: a loop process that is waiting starts a new sampling round
LoopSample ==
    /\ \E p \in SlushLoopProcess :
          LET n == NodeOfLoop(p) IN
          /\ pcLoop[p] = "wait"
          /\ colour[n] # NoColor
          /\ sampleSet == CHOOSE S \in SUBSET (Node \ {n}) :
                              Cardinality(S) = SampleSetSize
          /\ sample' = [sample EXCEPT ![p] = sampleSet]
          /\ msgs' = msgs \cup
                { [type   |-> "query",
                   src    |-> p,
                   dst    |-> QueryOfNode(qNode),
                   colour |-> colour[n] ] :
                      qNode \in sampleSet }
          /\ pcLoop' = [pcLoop EXCEPT ![p] = "tally"]
          /\ UNCHANGED <<colour, pcQuery, iter>>

\* ----------------------------------------------------------------------
\* Action: a query process replies to a query message
QueryRespond ==
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ q \in SlushQueryProcess
          /\ m.dst = q
          LET n == NodeOfQuery(q) IN
          /\ IF colour[n] = NoColor
                THEN colour' = [colour EXCEPT ![n] = m.colour]
                ELSE colour' = colour
          /\ reply == [type   |-> "reply",
                       src    |-> q,
                       dst    |-> m.src,
                       colour |-> colour'[n]]
          /\ msgs' = (msgs \ {m}) \cup {reply}
          /\ UNCHANGED <<pcLoop, pcQuery, sample, iter>>

\* ----------------------------------------------------------------------
\* Action: a loop process tallies the replies it has received
LoopTally ==
    /\ \E p \in SlushLoopProcess :
          LET n == NodeOfLoop(p) IN
          /\ pcLoop[p] = "tally"
          /\ sample[p] /= {}
          /\ \A node \in sample[p] :
                \E r \in msgs :
                    /\ r.type = "reply"
                    /\ r.dst  = p
                    /\ r.src  = QueryOfNode(node)
          /\ replies == { r \in msgs :
                           r.type = "reply" /\ r.dst = p }
          /\ redCnt  == Cardinality({ r \in replies : r.colour = "Red" })
          /\ blueCnt == Cardinality({ r \in replies : r.colour = "Blue" })
          /\ newCol ==
                IF redCnt >= PickFlipThreshold THEN "Red"
                ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                ELSE colour[n]
          /\ colour' = [colour EXCEPT ![n] = newCol]
          /\ iter'   = [iter EXCEPT ![p] = @ + 1]
          /\ sample' = [sample EXCEPT ![p] = {}]
          /\ IF iter'[p] = SlushIterationCount
                THEN pcLoop' = [pcLoop EXCEPT ![p] = "done"]
                ELSE pcLoop' = [pcLoop EXCEPT ![p] = "wait"]
          /\ msgs'   = msgs \ { r \in msgs :
                                 r.type = "reply" /\ r.dst = p }
          /\ UNCHANGED <<pcQuery>>

\* ----------------------------------------------------------------------
\* Action: when all loop processes are done, query processes finish
QueryExit ==
    /\ \A p \in SlushLoopProcess : pcLoop[p] = "done"
    /\ pcQuery' = [q \in SlushQueryProcess |-> "done"]
    /\ UNCHANGED <<colour, msgs, sample, iter, pcLoop>>

\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ LoopSample
    \/ QueryRespond
    \/ LoopTally
    \/ QueryExit

\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant required by the configuration
TypeInvariant ==
    /\ colour \in [Node -> (Colors \cup {NoColor})]
    /\ msgs   \subseteq Message
    /\ pcLoop \in [SlushLoopProcess -> {"wait","sample","tally","done"}]
    /\ pcQuery\in [SlushQueryProcess -> {"reply","done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====