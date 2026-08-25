---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,               \* set of all node identifiers
    SlushLoopProcess,   \* one loop process per node
    SlushQueryProcess,  \* one query process per node
    HostMapping,        \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,\* number of iterations each loop process must run
    SampleSetSize,      \* size of the peer sample taken each round
    PickFlipThreshold,  \* minimum number of identical replies needed to flip
    NoColor,            \* sentinel value meaning “uncolored”
    NoMessage           \* sentinel value for “no message”

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue", NoColor}

MessageType == {"query", "reply", "terminate"}

Message == [type : MessageType,
            src  : (SlushLoopProcess \cup SlushQueryProcess),
            dst  : (SlushLoopProcess \cup SlushQueryProcess),
            col  : Colors]

MessageSet == { m \in Message :
                /\ m.type \in MessageType
                /\ m.src  \in (SlushLoopProcess \cup SlushQueryProcess)
                /\ m.dst  \in (SlushLoopProcess \cup SlushQueryProcess)
                /\ m.col  \in Colors }

ProcSet == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,   \* [node \in Node |-> Colors]  current color of each node
    msgs,    \* set of in‑flight messages (subset of MessageSet)
    pc,      \* [proc \in ProcSet |-> ProcState] program counter per process
    sample,  \* [lp \in SlushLoopProcess |-> SUBSET Node] current sample set
    iter,    \* [lp \in SlushLoopProcess |-> Nat]    completed iterations

\* ----------------------------------------------------------------------
\* Enumerated program‑counter values
\* ----------------------------------------------------------------------
\* Client process
ClientPC == {"Assign", "Done"}

\* Loop processes
LoopPC == {"WaitColor", "Sample", "WaitReplies", "Update", "Terminate", "Done"}

\* Query processes
QueryPC == {"ReplyLoop", "Done"}

ProcState == UNION { ClientPC, LoopPC, QueryPC }

\* ----------------------------------------------------------------------
\* Helper functions to navigate HostMapping
\* ----------------------------------------------------------------------
NodeOfLoop(lp) == 
    CHOOSE n \in Node : <<n, lp, _>> \in HostMapping

QueryProcOfNode(n) ==
    CHOOSE qp \in SlushQueryProcess : <<n, _, qp>> \in HostMapping

LoopProcOfNode(n) ==
    CHOOSE lp \in SlushLoopProcess : <<n, lp, _>> \in HostMapping

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc     = [p \in ProcSet |-> 
                    IF p = "Client" THEN "Assign"
                    ELSE IF p \in SlushLoopProcess THEN "WaitColor"
                    ELSE "ReplyLoop"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ pc["Client"] = "Assign"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in {"Red", "Blue"} :
        /\ color' = [color EXCEPT ![n] = c]
        /\ UNCHANGED <<msgs, sample, iter>>
        /\ pc' = [pc EXCEPT !["Client"] = "Assign"]  \* stay in Assign until all nodes colored
    /\ UNCHANGED pc

\* When all nodes are colored the client moves to Done
ClientDone ==
    /\ pc["Client"] = "Assign"
    /\ \A n \in Node : color[n] # NoColor
    /\ pc' = [pc EXCEPT !["Client"] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* 2. Loop process waits until its node is colored
LoopRequireColor(lp) ==
    /\ pc[lp] = "WaitColor"
    /\ LET n == NodeOfLoop(lp) IN color[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* 3. Loop process selects a random sample and sends queries
LoopSample(lp) ==
    /\ pc[lp] = "Sample"
    /\ LET n  == NodeOfLoop(lp)
           others == Node \ {n}
           s  == CHOOSE s \in SUBSET others : Cardinality(s) = SampleSetSize
    IN  /\ sample' = [sample EXCEPT ![lp] = s]
        /\ msgs' = msgs \cup {
                [type |-> "query",
                 src  |-> lp,
                 dst  |-> QueryProcOfNode(p),
                 col  |-> color[n]]
                : p \in s
            }
        /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
        /\ UNCHANGED <<color, iter>>

\* 4. Query process responds to a query (adopts color if uncolored)
RespondQuery(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.dst  = qp
          /\ LET n == CHOOSE n \in Node :
                 <<n, _, qp>> \in HostMapping
             curCol == color[n]
          IN  /\ IF curCol = NoColor
                THEN color' = [color EXCEPT ![n] = m.col]
                ELSE UNCHANGED color
          /\ reply == [type |-> "reply",
                       src  |-> qp,
                       dst  |-> m.src,
                       col  |-> (IF curCol = NoColor THEN m.col ELSE curCol)]
          /\ msgs' = (msgs \ {m}) \cup {reply}
          /\ UNCHANGED <<sample, iter, pc>>
    /\ UNCHANGED pc

\* 5. Loop process tallies replies and possibly flips its color
LoopTally(lp) ==
    /\ pc[lp] = "WaitReplies"
    /\ LET s   == sample[lp]
           n   == NodeOfLoop(lp)
           replies == { m \in msgs :
                         /\ m.type = "reply"
                         /\ m.dst  = lp
                         /\ m.src \in { QueryProcOfNode(p) : p \in s } }
    IN  /\ Cardinality(replies) = SampleSetSize
        /\ reds   == Cardinality({ r \in replies : r.col = "Red" })
        /\ blues  == Cardinality({ r \in replies : r.col = "Blue" })
        /\ newCol == 
              IF reds >= PickFlipThreshold THEN "Red"
              ELSE IF blues >= PickFlipThreshold THEN "Blue"
              ELSE color[n]
        /\ color' = [color EXCEPT ![n] = newCol]
        /\ sample' = [sample EXCEPT ![lp] = {}]
        /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
        /\ msgs'   = msgs \ replies   \* remove processed replies
        /\ pc' = [pc EXCEPT ![lp] = 
                     IF iter'[lp] = SlushIterationCount
                     THEN "Terminate"
                     ELSE "Sample"]
        /\ UNCHANGED <<>>

\* 6. Loop process broadcasts termination
LoopTerminate(lp) ==
    /\ pc[lp] = "Terminate"
    /\ msgs' = msgs \cup {
            [type |-> "terminate",
             src  |-> lp,
             dst  |-> qp,
             col  |-> NoColor]
            : qp \in SlushQueryProcess
        }
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sample, iter>>

\* 7. Query processes exit when every loop has terminated
QueryExit(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \A lp \in SlushLoopProcess :
          \E m \in msgs :
                /\ m.type = "terminate"
                /\ m.dst  = qp
                /\ m.src  = lp
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E lp \in SlushLoopProcess : LoopRequireColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopSample(lp)
    \/ \E qp \in SlushQueryProcess : RespondQuery(qp)
    \/ \E lp \in SlushLoopProcess : LoopTally(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ ClientAssign
    \/ ClientDone

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> Colors]
    /\ msgs \subseteq MessageSet
    /\ pc \in [ProcSet -> ProcState]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]

=============================================================================