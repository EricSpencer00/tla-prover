---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Node,               \* set of all node identifiers
  SlushLoopProcess,   \* one loop process per node
  SlushQueryProcess,  \* one query process per node
  HostMapping,        \* set of triples <<node, loopProc, queryProc>>
  SlushIterationCount,\* number of iterations each loop performs
  SampleSetSize,      \* size of the random peer sample
  PickFlipThreshold,  \* number of equal‑colored replies required to flip
  NoColor,            \* value representing “uncolored”
  NoMessage           \* placeholder for “no message”

\* ----------------------------------------------------------------------
\*  Colors used by the protocol
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\*  Message record type
\* ----------------------------------------------------------------------
Message == [type  : {"query", "reply", "term"},
            src   : (SlushLoopProcess \cup SlushQueryProcess),
            dst   : (SlushLoopProcess \cup SlushQueryProcess),
            color : (Colors \cup {NoColor})]

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES
  nodeColor,   \* [node \in Node |-> (Colors \cup {NoColor})]
  msgs,        \* subset of Message
  sampleSet,   \* [loopProc \in SlushLoopProcess |-> SUBSET Node]
  iterCount    \* [loopProc \in SlushLoopProcess |-> Nat]

\* ----------------------------------------------------------------------
\*  Helper functions that extract the node associated with a process
\* ----------------------------------------------------------------------
NodeOfLoop(p) ==
  CHOOSE n \in Node :
    \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping

NodeOfQuery(q) ==
  CHOOSE n \in Node :
    \E p \in SlushLoopProcess : <<n, p, q>> \in HostMapping

LoopOfNode(n) ==
  CHOOSE p \in SlushLoopProcess :
    \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping

QueryOfNode(n) ==
  CHOOSE q \in SlushQueryProcess :
    \E p \in SlushLoopProcess : <<n, p, q>> \in HostMapping

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ msgs      = {}
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterCount = [p \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\*  Type invariant required by the .cfg file
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ nodeColor \in [Node -> (Colors \cup {NoColor})]
  /\ msgs \subseteq Message

\* ----------------------------------------------------------------------
\*  Client: assigns a random color to an uncolored node
\* ----------------------------------------------------------------------
ClientAssign ==
  /\ \E n \in Node :
        /\ nodeColor[n] = NoColor
        /\ \E c \in Colors :
              /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\*  Loop process actions
\* ----------------------------------------------------------------------
LoopRequireColor(p) ==
  /\ nodeColor[NodeOfLoop(p)] # NoColor
  /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

LoopSample(p) ==
  /\ iterCount[p] < SlushIterationCount
  /\ LET others == Node \ {NodeOfLoop(p)} IN
       \E samp \in SUBSET others :
            /\ Cardinality(samp) = SampleSetSize
            /\ sampleSet' = [sampleSet EXCEPT ![p] = samp]
            /\ msgs' = msgs \cup
               { [type  |-> "query",
                  src   |-> p,
                  dst   |-> QueryOfNode(n),
                  color |-> nodeColor[NodeOfLoop(p)] ] :
                     n \in samp }
  /\ UNCHANGED <<nodeColor, iterCount>>

LoopReceiveReplies(p) ==
  /\ \A n \in sampleSet[p] :
        \E m \in msgs :
           /\ m.type = "reply"
           /\ m.dst  = p
           /\ m.src  = QueryOfNode(n)
  /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

LoopFlip(p) ==
  /\ iterCount[p] < SlushIterationCount
  /\ \A n \in sampleSet[p] :
        \E m \in msgs :
           /\ m.type = "reply"
           /\ m.dst  = p
           /\ m.src  = QueryOfNode(n)
  /\ LET replies == { m.color : m \in msgs /\ m.type = "reply" /\ m.dst = p } IN
     LET redCnt  == Cardinality({c \in replies : c = "Red"}) IN
     LET blueCnt == Cardinality({c \in replies : c = "Blue"}) IN
     /\ IF redCnt >= PickFlipThreshold THEN
            nodeColor' = [nodeColor EXCEPT ![NodeOfLoop(p)] = "Red"]
        ELSE IF blueCnt >= PickFlipThreshold THEN
            nodeColor' = [nodeColor EXCEPT ![NodeOfLoop(p)] = "Blue"]
        ELSE
            nodeColor' = nodeColor
  /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
  /\ iterCount' = [iterCount EXCEPT ![p] = @ + 1]
  /\ UNCHANGED msgs

LoopTerminate(p) ==
  /\ iterCount[p] = SlushIterationCount
  /\ msgs' = msgs \cup
       { [type  |-> "term",
          src   |-> p,
          dst   |-> q,
          color |-> NoColor] :
            q \in SlushQueryProcess }
  /\ UNCHANGED <<nodeColor, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\*  Query process actions
\* ----------------------------------------------------------------------
QueryRespond(q) ==
  /\ \E m \in msgs :
        /\ m.type = "query"
        /\ m.dst  = q
  /\ LET m == CHOOSE mm \in msgs :
                 /\ mm.type = "query"
                 /\ mm.dst = q
        IN
     LET n == NodeOfQuery(q) IN
     LET newCol ==
        IF nodeColor[n] = NoColor THEN m.color ELSE nodeColor[n] IN
     /\ nodeColor' = [nodeColor EXCEPT ![n] = newCol]
     /\ msgs' = (msgs \ {m}) \cup
                { [type  |-> "reply",
                   src   |-> q,
                   dst   |-> m.src,
                   color |-> newCol] }
  /\ UNCHANGED <<sampleSet, iterCount>>

QueryTerminateCheck(q) ==
  /\ \A p \in SlushLoopProcess :
        \E m \in msgs :
           /\ m.type = "term"
           /\ m.src  = p
           /\ m.dst  = q
  /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\*  Next-state relation (any enabled action may occur)
\* ----------------------------------------------------------------------
Next ==
  \/ ClientAssign
  \/ \E p \in SlushLoopProcess : LoopRequireColor(p)
  \/ \E p \in SlushLoopProcess : LoopSample(p)
  \/ \E p \in SlushLoopProcess : LoopReceiveReplies(p)
  \/ \E p \in SlushLoopProcess : LoopFlip(p)
  \/ \E p \in SlushLoopProcess : LoopTerminate(p)
  \/ \E q \in SlushQueryProcess : QueryRespond(q)
  \/ \E q \in SlushQueryProcess : QueryTerminateCheck(q)

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<nodeColor, msgs, sampleSet, iterCount>>

====