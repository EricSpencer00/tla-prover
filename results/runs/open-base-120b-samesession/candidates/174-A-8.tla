---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
CONSTANTS
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* set of loop‑process identifiers
    SlushQueryProcess,   \* set of query‑process identifiers
    HostMapping,         \* set of triples <<loop, query, node>>
    SlushIterationCount, \* number of iterations each loop performs
    SampleSetSize,       \* size of the random sample per round
    PickFlipThreshold,   \* number of replies of one color needed to flip
    NoColor,             \* sentinel for an uncolored node
    NoMessage            \* sentinel for the absence of a message

\* ----------------------------------------------------------------------
\* Concrete data definitions
Colors == {"Red", "Blue"}

MessageType == {"Query", "Reply", "Terminate"}

\* A message is a record with fields:
\*   type \in MessageType
\*   src  \in (SlushLoopProcess \cup SlushQueryProcess)
\*   dst  \in (SlushLoopProcess \cup SlushQueryProcess)
\*   col  \in Colors \cup {NoColor}
Message ==
    [type : MessageType,
     src  : (SlushLoopProcess \cup SlushQueryProcess),
     dst  : (SlushLoopProcess \cup SlushQueryProcess),
     col  : Colors \cup {NoColor}]

MessageSet ==
    { m \in Message :
        /\ (m.type = "Query")    => (m.col \in Colors)
        /\ (m.type = "Reply")    => (m.col \in Colors \cup {NoColor})
        /\ (m.type = "Terminate")=> (m.col = NoMessage) }

\* ----------------------------------------------------------------------
\* Helper functions to navigate HostMapping (which is a set of triples)
\* Each element of HostMapping is a tuple <<lp, qp, n>>
LoopNode(lp) ==
    LET t == CHOOSE t \in HostMapping : t[1] = lp IN t[3]

QueryNodeInv(n) ==
    CHOOSE t \in HostMapping : t[3] = n IN t[2]

\* ----------------------------------------------------------------------
\* Process state enumeration
ProcState == {"Init", "WaitingColor", "Sample", "Collect", "Done"}

VARIABLES
    color,   \* [Node -> (Colors \cup {NoColor})]
    msgs,    \* set of Message
    pc,      \* [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> ProcState]
    sample,  \* [lp \in SlushLoopProcess -> SUBSET Node]   \* current sample set
    iter     \* [lp \in SlushLoopProcess -> Nat]           \* completed iterations

vars == <<color, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]
    /\ pc = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> "Init"]
    /\ \A lp \in SlushLoopProcess : pc[lp] = "WaitingColor"
    /\ \A qp \in SlushQueryProcess : pc[qp] = "Collect"
    /\ pc["Client"] = "Init"

\* ----------------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ pc["Client"] = "Init"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in Colors :
         LET n == CHOOSE n \in Node : color[n] = NoColor IN
         /\ color' = [color EXCEPT ![n] = c]
         /\ msgs'   = msgs
         /\ sample' = sample
         /\ iter'   = iter
         /\ pc'     = pc

\* ----------------------------------------------------------------------
\* 2. Loop process waits until its host node has a color
LoopRequireColor ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "WaitingColor"
        /\ LET n == LoopNode(lp) IN color[n] # NoColor
        /\ pc' = [pc EXCEPT ![lp] = "Sample"]
        /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* 3. Loop process samples peers and sends query messages
LoopSample ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "Sample"
        /\ LET n == LoopNode(lp) IN
           \E s \subseteq Node \ {n} :
               /\ Cardinality(s) = SampleSetSize
               /\ sample' = [sample EXCEPT ![lp] = s]
               /\ msgs' = msgs \cup
                         { [type |-> "Query",
                            src  |-> lp,
                            dst  |-> QueryNodeInv(m),
                            col  |-> color[n]]
                           : m \in s }
               /\ pc' = [pc EXCEPT ![lp] = "Collect"]
               /\ UNCHANGED <<color, iter>>

\* ----------------------------------------------------------------------
\* 4. Query process answers a received query (adopting the color if uncolored)
QueryRespond ==
    \E qp \in SlushQueryProcess :
        /\ pc[qp] = "Collect"
        /\ \E m \in msgs :
              /\ m.type = "Query" /\ m.dst = qp
              /\ LET n   == QueryNodeInv(m.src)   \* node owned by qp
                 cur == color[n] IN
                 /\ IF cur = NoColor THEN
                        color' = [color EXCEPT ![n] = m.col]
                    ELSE
                        color' = color
                 /\ msgs' = (msgs \ {m}) \cup
                           { [type |-> "Reply",
                              src  |-> qp,
                              dst  |-> m.src,
                              col  |-> IF cur = NoColor THEN m.col ELSE cur] }
                 /\ sample' = sample
                 /\ iter'   = iter
                 /\ pc'     = pc
                 /\ UNCHANGED <<sample, iter>>

\* ----------------------------------------------------------------------
\* 5. Loop process tallies replies and possibly flips its node's color
LoopTally ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "Collect"
        /\ LET s == sample[lp] IN s # {}
        /\ \A node \in s :
              \E r \in msgs :
                 /\ r.type = "Reply"
                 /\ r.dst  = lp
                 /\ r.src  = QueryNodeInv(node)
        /\ LET replies   == { r \in msgs : r.type = "Reply" /\ r.dst = lp } IN
           redCount  == Cardinality({ r \in replies : r.col = "Red" })  /\ 
           blueCount == Cardinality({ r \in replies : r.col = "Blue" }) /\ 
           curNode   == LoopNode(lp) IN
           /\ IF redCount >= PickFlipThreshold THEN
                  color' = [color EXCEPT ![curNode] = "Red"]
              ELSE IF blueCount >= PickFlipThreshold THEN
                  color' = [color EXCEPT ![curNode] = "Blue"]
              ELSE
                  color' = color
        /\ msgs'   = msgs \ replies
        /\ sample' = [sample EXCEPT ![lp] = {}]
        /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
        /\ pc' = [pc EXCEPT ![lp] =
                     IF iter'[lp] = SlushIterationCount
                        THEN "Done"
                        ELSE "Sample"]
        /\ UNCHANGED <<color, msgs, sample, iter>> \* (already handled)

\* ----------------------------------------------------------------------
\* 6. Loop process broadcasts termination after finishing its iterations
LoopTerminate ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "Done"
        /\ msgs' = msgs \cup
                  { [type |-> "Terminate",
                     src  |-> lp,
                     dst  |-> qp,
                     col  |-> NoMessage] : qp \in SlushQueryProcess }
        /\ pc'   = pc
        /\ UNCHANGED <<color, sample, iter>>

\* ----------------------------------------------------------------------
\* 7. Query process exits when it has received termination from every loop
QueryExit ==
    \E qp \in SlushQueryProcess :
        /\ pc[qp] = "Collect"
        /\ \A lp \in SlushLoopProcess :
              \E m \in msgs :
                 /\ m.type = "Terminate"
                 /\ m.dst  = qp
                 /\ m.src  = lp
        /\ pc' = [pc EXCEPT ![qp] = "Done"]
        /\ msgs' = msgs \ { m \in msgs : m.type = "Terminate" /\ m.dst = qp }
        /\ UNCHANGED <<color, sample, iter>>

\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ LoopRequireColor
    \/ LoopSample
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryExit

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type safety invariant
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs  \subseteq MessageSet
    /\ pc    \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> ProcState]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [SlushLoopProcess -> Nat]

====