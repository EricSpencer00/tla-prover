---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* set of loop process identifiers (one per node)
    SlushQueryProcess,   \* set of query process identifiers (one per node)
    HostMapping,         \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* maximum number of iterations each loop performs
    SampleSetSize,       \* size of the random sample each iteration
    PickFlipThreshold,   \* number of same‑color replies needed to flip
    NoColor,             \* special value meaning “uncolored”
    NoMessage            \* sentinel for “no message” (not used directly)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,   \* [node \in Node |-> NoColor \/ "Red" \/ "Blue"]
    msgs,    \* set of in‑flight messages
    pc,      \* [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> pc‑value]
    sample,  \* [lp \in SlushLoopProcess |-> SUBSET Node]   (* peers sampled this round *)
    iter     \* [lp \in SlushLoopProcess |-> Nat]          (* iterations already done *)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue", NoColor}
MessageTypes == {"Query", "Reply", "Terminate"}

Message == [type : MessageTypes,
            src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
            dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"} \cup {"AllQueries"}),
            col  : Colors]

IsQuery(m) == m.type = "Query"
IsReply(m) == m.type = "Reply"
IsTerminate(m) == m.type = "Terminate"

\* Host relations derived from HostMapping
NodeOfLoop(lp) ==
    CHOOSE n \in Node : <<n, lp, _>> \in HostMapping

NodeOfQuery(qp) ==
    CHOOSE n \in Node : <<n, _, qp>> \in HostMapping

QueryOfNode(n) ==
    CHOOSE qp \in SlushQueryProcess : <<n, _, qp>> \in HostMapping

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]
    /\ pc     = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 
                 IF p = "Client"          THEN "ClientReady"
                 ELSE IF p \in SlushLoopProcess THEN "WaitColor"
                 ELSE "ReplyLoop"]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ pc["Client"] = "ClientReady"
    /\ \E n \in Node : color[n] = NoColor
    /\ LET uncolored == { n \in Node : color[n] = NoColor } IN
       /\ n \in uncolored
       /\ col \in {"Red","Blue"}
       /\ color' = [color EXCEPT ![n] = col]
       /\ pc'    = [pc EXCEPT !["Client"] = "ClientReady"]
       /\ UNCHANGED <<msgs, sample, iter>>

\* 2. Loop process waits until its node gets a color
LoopRequireColor(lp) ==
    /\ pc[lp] = "WaitColor"
    /\ LET n == NodeOfLoop(lp) IN
       /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = "Sample"]
       /\ UNCHANGED <<color, msgs, sample, iter>>

\* 3. Loop process creates a sample and sends queries
LoopQuery(lp) ==
    /\ pc[lp] = "Sample"
    /\ LET n == NodeOfLoop(lp) IN
       /\ nColor == color[n]
       /\ otherNodes == { m \in Node : m # n }
       /\ sampleSet  == CHOOSE s \in SUBSET otherNodes : Cardinality(s) = SampleSetSize
       /\ msgs'  = msgs \cup { [type |-> "Query",
                               src  |-> lp,
                               dst  |-> QueryOfNode(m),
                               col  |-> nColor] : m \in sampleSet }
       /\ sample' = [sample EXCEPT ![lp] = sampleSet]
       /\ pc'    = [pc EXCEPT ![lp] = "Collect"]
       /\ UNCHANGED <<color, iter>>

\* 4. Query process receives a query and replies (adopts if uncolored)
QueryRespond(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \E m \in msgs : IsQuery(m) /\ m.dst = qp
    /\ LET qmsg == CHOOSE m \in msgs : IsQuery(m) /\ m.dst = qp
           n    == NodeOfQuery(qp)
           cur  == color[n]
           new  == IF cur = NoColor THEN qmsg.col ELSE cur
           reply == [type |-> "Reply",
                     src  |-> qp,
                     dst  |-> qmsg.src,
                     col  |-> new]
       IN
          /\ color' = [color EXCEPT ![n] = new]
          /\ msgs'   = (msgs \ {qmsg}) \cup {reply}
          /\ pc'     = [pc EXCEPT ![qp] = "ReplyLoop"]
          /\ UNCHANGED <<sample, iter>>

\* 5. Loop process collects replies, possibly flips, then continues or terminates
LoopCollect(lp) ==
    /\ pc[lp] = "Collect"
    /\ LET n       == NodeOfLoop(lp)
           sSet    == sample[lp]
           replies == { m \in msgs : IsReply(m) /\ m.dst = lp /\ m.src \in { QueryOfNode(p) : p \in sSet } }
           cntRed  == Cardinality({ r \in replies : r.col = "Red" })
           cntBlue == Cardinality({ r \in replies : r.col = "Blue" })
           newIter == iter[lp] + 1
           newColor == IF cntRed >= PickFlipThreshold THEN "Red"
                       ELSE IF cntBlue >= PickFlipThreshold THEN "Blue"
                       ELSE color[n]
       IN
          /\ Cardinality(replies) = Cardinality(sSet)
          /\ color'  = [color EXCEPT ![n] = newColor]
          /\ msgs'   = msgs \ replies
          /\ sample' = [sample EXCEPT ![lp] = {}]
          /\ iter'   = [iter EXCEPT ![lp] = newIter]
          /\ pc'     = [pc EXCEPT ![lp] = 
                         IF newIter < SlushIterationCount
                         THEN "Sample"
                         ELSE "Terminate"]
          /\ UNCHANGED <<pc, sample, iter>>  \* pc already updated above

\* 6. Loop process broadcasts termination after finishing all iterations
LoopTerminate(lp) ==
    /\ pc[lp] = "Terminate"
    /\ LET termMsg == [type |-> "Terminate",
                       src  |-> lp,
                       dst  |-> "AllQueries",
                       col  |-> NoColor]
       IN
          /\ msgs' = msgs \cup {termMsg}
          /\ pc'   = [pc EXCEPT ![lp] = "Done"]
          /\ UNCHANGED <<color, sample, iter>>

\* 7. Query processes exit when they have seen termination from every loop
QueryExit(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \A lp \in SlushLoopProcess : \E m \in msgs : IsTerminate(m) /\ m.src = lp
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E lp \in SlushLoopProcess : LoopRequireColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopQuery(lp)
    \/ \E qp \in SlushQueryProcess : QueryRespond(qp)
    \/ \E lp \in SlushLoopProcess : LoopCollect(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ ClientAssign

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<color, msgs, pc, sample, iter>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> Colors]
    /\ msgs   \subseteq Message
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) ->
                {"ClientReady","WaitColor","Sample","Collect","Terminate","Done","ReplyLoop"} ]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [SlushLoopProcess -> Nat]

====