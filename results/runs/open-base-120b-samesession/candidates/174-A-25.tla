---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* set of loop process identifiers (one per node)
    SlushQueryProcess,   \* set of query process identifiers (one per node)
    HostMapping,         \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* number of iterations each loop process must perform
    SampleSetSize,       \* size of the peer sample taken each round
    PickFlipThreshold,   \* threshold for adopting a color
    NoColor,             \* special value meaning “uncolored”
    NoMessage            \* placeholder for “no message”

\* ----------------------------------------------------------------------
\* Derived constants
ColorSet == {"Red", "Blue"}

Proc == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Message == [type   : {"query", "reply", "term"},
            from   : Proc,
            to     : Proc,
            color  : ColorSet \cup {NoColor}]

\* ----------------------------------------------------------------------
\* Helper functions extracting the node that a given loop or query process
\* “hosts”, based on HostMapping.
NodeOfLoop(l) ==
    CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

NodeOfQuery(q) ==
    CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    color,   \* [node -> (ColorSet \cup {NoColor})]
    msgs,    \* set of messages in transit
    sample,  \* [loopProc -> SUBSET(Node)] – current peer sample for each loop
    iter,    \* [loopProc -> Nat] – iteration counter for each loop
    pc       \* [process -> {"Start","Sample","WaitReplies","Done"}]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ iter   = [l \in SlushLoopProcess |-> 0]
    /\ pc    = [p \in Proc |-> "Start"]

\* ----------------------------------------------------------------------
\* Actions

\* ----- Client assigns a random color to an uncolored node ----------------
ClientAssign ==
    /\ pc["Client"] = "Start"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E col \in ColorSet :
          /\ color' = [color EXCEPT ![n] = col]
          /\ pc'    = [pc EXCEPT !["Client"] = "Start"]
          /\ UNCHANGED <<msgs, sample, iter>>

\* ----- Loop process waits until its host node is colored -----------------
LoopStart(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "Start"
    /\ LET n == NodeOfLoop(l) IN
          /\ color[n] # NoColor
          /\ pc' = [pc EXCEPT ![l] = "Sample"]
          /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----- Loop process picks a random sample and sends queries -------------
LoopSample(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "Sample"
    /\ LET n == NodeOfLoop(l) IN
          \E s \in SUBSET(Node \ {n}) :
                /\ Cardinality(s) = SampleSetSize
                /\ sample' = [sample EXCEPT ![l] = s]
                /\ msgs'   = msgs \cup
                              { [type |-> "query",
                                 from |-> l,
                                 to   |-> q,
                                 color|-> color[n]] : q \in s }
                /\ pc'     = [pc EXCEPT ![l] = "WaitReplies"]
                /\ UNCHANGED <<color, iter>>

\* ----- Loop process receives all replies, possibly flips its color -------
LoopWait(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "WaitReplies"
    /\ LET n == NodeOfLoop(l) IN
          LET reps == { m \in msgs : m.type = "reply" /\ m.to = l } IN
               /\ Cardinality(reps) = Cardinality(sample[l])
               /\ LET redCnt  == Cardinality({ r \in reps : r.color = "Red" })
                      blueCnt == Cardinality({ r \in reps : r.color = "Blue" })
                      newCol  == IF redCnt >= PickFlipThreshold
                                 THEN "Red"
                                 ELSE IF blueCnt >= PickFlipThreshold
                                      THEN "Blue"
                                      ELSE color[n] IN
                 /\ color' = [color EXCEPT ![n] = newCol]
                 /\ sample' = [sample EXCEPT ![l] = {}]
                 /\ iter'   = [iter EXCEPT ![l] = iter[l] + 1]
                 /\ msgsTmp = msgs \ { m \in msgs : m.type = "reply" /\ m.to = l }
                 /\ IF iter'[l] = SlushIterationCount
                    THEN /\ pc' = [pc EXCEPT ![l] = "Done"]
                         /\ msgs' = msgsTmp \cup
                                   { [type |-> "term",
                                      from |-> l,
                                      to   |-> "All",
                                      color|-> NoColor] }
                    ELSE /\ pc' = [pc EXCEPT ![l] = "Sample"]
                         /\ msgs' = msgsTmp
                 /\ UNCHANGED <<>>

\* ----- Query process answers a single incoming query --------------------
QueryRespond(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = "Start"
    /\ \E m \in msgs : m.type = "query" /\ m.to = q
    /\ LET n == NodeOfQuery(q) IN
       \E col \in (IF color[n] = NoColor THEN {m.color} ELSE {color[n]}) :
            /\ color' = [color EXCEPT ![n] = col]
            /\ msgs' = (msgs \ {m}) \cup
                       { [type |-> "reply",
                          from |-> q,
                          to   |-> m.from,
                          color|-> col] }
            /\ UNCHANGED <<sample, iter, pc>>

\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ \E l \in SlushLoopProcess : LoopStart(l)
    \/ \E l \in SlushLoopProcess : LoopSample(l)
    \/ \E l \in SlushLoopProcess : LoopWait(l)
    \/ \E q \in SlushQueryProcess : QueryRespond(q)

\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sample, iter, pc>>

\* ----------------------------------------------------------------------
\* Type invariant required by the configuration
TypeInvariant ==
    /\ color \in [Node -> (ColorSet \cup {NoColor})]
    /\ msgs  \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET(Node)]
    /\ iter   \in [SlushLoopProcess -> Nat]
    /\ pc \in [Proc -> {"Start","Sample","WaitReplies","Done"}]

====