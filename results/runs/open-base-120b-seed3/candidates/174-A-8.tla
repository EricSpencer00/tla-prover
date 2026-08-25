---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

(*-------------------------------------------------------------------*)
(* CONSTANTS *)
CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers
    SlushQueryProcess,  \* Set of query process identifiers
    HostMapping,        \* Set of triples <<node, loop, query>>
    SlushIterationCount,\* Number of iterations each loop process performs
    SampleSetSize,      \* Size of the peer sample taken each round
    PickFlipThreshold,  \* Threshold needed to flip to a color
    NoColor,            \* Symbol representing an uncolored node
    NoMessage           \* Symbol representing the absence of a message

(*-------------------------------------------------------------------*)
(* DERIVED SETS *)
AllProcesses == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

(*-------------------------------------------------------------------*)
(* HELPERS *)

NodeOfLoop(lp) == 
    CHOOSE hm \in HostMapping : hm[2] = lp
NodeOfQuery(qp) ==
    CHOOSE hm \in HostMapping : hm[3] = qp
NodeOfProcess(p) ==
    IF p \in SlushLoopProcess THEN NodeOfLoop(p)
    ELSE IF p \in SlushQueryProcess THEN NodeOfQuery(p)
    ELSE NoMessage

LoopOfNode(n) ==
    CHOOSE hm \in HostMapping : hm[1] = n
QueryOfNode(n) ==
    CHOOSE hm \in HostMapping : hm[1] = n

Colors == {"Red", "Blue"}

Message ==
    [type : {"Query", "Reply", "Term"},
     src  : AllProcesses,
     dst  : AllProcesses,
     color: Colors]

MessageSet == { m \in Message :
                 \/ m.type = "Query" /\ m.src \in SlushLoopProcess /\ m.dst \in SlushQueryProcess
                 \/ m.type = "Reply" /\ m.src \in SlushQueryProcess /\ m.dst \in SlushLoopProcess
                 \/ m.type = "Term"  /\ m.src \in SlushLoopProcess  /\ m.dst = "All" }

(*-------------------------------------------------------------------*)
(* STATE VARIABLES *)

VARIABLES
    color,   \* [Node -> (NoColor \cup Colors)]
    msgs,    \* Subset of MessageSet
    pc,      \* [AllProcesses -> PCState]
    sample,  \* [SlushLoopProcess -> SUBSET Node]  (current sampled peers)
    iter     \* [SlushLoopProcess -> Nat]         (iterations completed)

PCState == {"Assign", "Done", "WaitColor", "Iterate", "Collect", "Terminate", "ReplyLoop"}

(*-------------------------------------------------------------------*)
(* INITIAL STATE *)

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in AllProcesses |
                 IF p = "Client" THEN "Assign"
                 ELSE IF p \in SlushLoopProcess THEN "WaitColor"
                 ELSE "ReplyLoop"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

(*-------------------------------------------------------------------*)
(* ACTIONS *)

(* Client assigns a random color to an uncolored node *)
ClientAssign ==
    /\ pc["Client"] = "Assign"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in Colors :
        LET col' == [color EXCEPT ![n] = c] IN
        /\ color' = col'
        /\ pc'    = [pc EXCEPT !["Client"] = 
                        (IF \A n2 \in Node : col'[n2] # NoColor THEN "Done" ELSE "Assign")]
        /\ UNCHANGED <<msgs, sample, iter>>

(* Client finishes once every node is colored *)
ClientDone ==
    /\ pc["Client"] = "Assign"
    /\ \A n \in Node : color[n] # NoColor
    /\ pc' = [pc EXCEPT !["Client"] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(* Loop process waits until its node has a color *)
LoopRequireColor ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "WaitColor"
        /\ LET n == NodeOfLoop(lp) IN color[n] # NoColor
        /\ pc' = [pc EXCEPT ![lp] = "Iterate"]
        /\ UNCHANGED <<color, msgs, sample, iter>>

(* Loop process creates a sample set and sends queries *)
LoopQuery ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "Iterate"
        /\ iter[lp] < SlushIterationCount
        /\ LET n   == NodeOfLoop(lp)
               curC == color[n]
               peers == Node \ {n}
               sSet  == CHOOSE s \subseteq peers : Cardinality(s) = SampleSetSize
               qpSet == { q \in SlushQueryProcess : NodeOfQuery(q) \in sSet }
               newMsgs == { [type |-> "Query", src |-> lp, dst |-> q, color |-> curC] : q \in qpSet }
           IN
               /\ msgs'   = msgs \cup newMsgs
               /\ sample' = [sample EXCEPT ![lp] = sSet]
               /\ pc'     = [pc EXCEPT ![lp] = "Collect"]
               /\ UNCHANGED <<color, iter>>

(* Query process responds to a query, possibly adopting the queried color *)
QueryRespond ==
    \E q \in SlushQueryProcess :
        /\ pc[q] = "ReplyLoop"
        /\ \E m \in msgs :
              /\ m.type = "Query"
              /\ m.dst  = q
              /\ LET n          == NodeOfQuery(q)
                     incomingC  == m.color
                     curC       == color[n]
                     adoptedC   == IF curC = NoColor THEN incomingC ELSE curC
                     reply      == [type |-> "Reply", src |-> q, dst |-> m.src, color |-> adoptedC]
                 IN
                     /\ color' = [color EXCEPT ![n] = adoptedC]
                     /\ msgs'  = (msgs \ {m}) \cup {reply}
                     /\ pc'    = [pc EXCEPT ![q] = "ReplyLoop"]
                     /\ UNCHANGED <<sample, iter>>

(* Loop process tallies replies, possibly flips its node's color *)
LoopTally ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "Collect"
        /\ LET expectedReplies == 
                { q \in SlushQueryProcess : NodeOfQuery(q) \in sample[lp] }
               receivedReplies  ==
                { m \in msgs : m.type = "Reply" /\ m.dst = lp }
           IN
               /\ Cardinality(receivedReplies) = SampleSetSize
               /\ \A q \in expectedReplies : 
                     \E m \in receivedReplies : m.src = q
               /\ LET reds   == Cardinality({ m \in receivedReplies : m.color = "Red" })
                      blues  == Cardinality({ m \in receivedReplies : m.color = "Blue" })
                      n      == NodeOfLoop(lp)
                      curC   == color[n]
                      newC   == IF reds >= PickFlipThreshold THEN "Red"
                               ELSE IF blues >= PickFlipThreshold THEN "Blue"
                               ELSE curC
                  IN
                      /\ color' = [color EXCEPT ![n] = newC]
                      /\ msgs'  = msgs \ receivedReplies   \* consumed replies
                      /\ sample' = [sample EXCEPT ![lp] = {}]
                      /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
                      /\ IF iter'[lp] = SlushIterationCount
                           THEN pc' = [pc EXCEPT ![lp] = "Terminate"]
                           ELSE pc' = [pc EXCEPT ![lp] = "Iterate"]
                      /\ UNCHANGED pc

(* Loop process broadcasts termination message and goes done *)
LoopTerminate ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "Terminate"
        /\ msgs' = msgs \cup { [type |-> "Term", src |-> lp, dst |-> "All", color |-> NoColor] }
        /\ pc'   = [pc EXCEPT ![lp] = "Done"]
        /\ UNCHANGED <<color, sample, iter>>

(* Query processes exit when all loop processes are done *)
QueryExit ==
    \E q \in SlushQueryProcess :
        /\ pc[q] = "ReplyLoop"
        /\ \A lp \in SlushLoopProcess : pc[lp] = "Done"
        /\ pc' = [pc EXCEPT ![q] = "Done"]
        /\ UNCHANGED <<color, msgs, sample, iter>>

(*-------------------------------------------------------------------*)
(* NEXT RELATION *)

Next ==
    \/ ClientAssign
    \/ ClientDone
    \/ LoopRequireColor
    \/ LoopQuery
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryExit

(*-------------------------------------------------------------------*)
(* SPECIFICATION *)

vars == <<color, msgs, pc, sample, iter>>

Spec == Init /\ [][Next]_vars

(*-------------------------------------------------------------------*)
(* INVARIANTS *)

TypeInvariant ==
    /\ color \in [Node -> (NoColor \cup Colors)]
    /\ msgs \subseteq MessageSet

(*-------------------------------------------------------------------*)
(* THEOREMS / PROPERTIES *)

THEOREM Spec => []TypeInvariant

====