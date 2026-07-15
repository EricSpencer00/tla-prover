---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANTS 
    Node,               \* Set of all node identifiers
    SlushLoopProcess,   \* Set of all loop process identifiers
    SlushQueryProcess,  \* Set of all query process identifiers
    HostMapping,        \* Set of triples <<proc, "Loop"/"Query", node>>
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Number of peers sampled each round
    PickFlipThreshold,  \* Minimum number of matching replies needed to flip
    NoColor,            \* Special value representing "uncolored"
    NoMessage           \* Special value representing "no message"

(***************************************************************************)
(* Derived constants                                                       *)
(***************************************************************************)
Colors == {"Red", "Blue"}

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)
VARIABLES 
    color,          \* [node -> color ∪ {NoColor}]
    msgs,           \* Set of in‑flight messages
    pc,             \* [proc -> pcLabel]
    sample,         \* [loopProc -> SUBSET Node]  (current sample set)
    iter            \* [loopProc -> Nat] (iterations completed)

(***************************************************************************)
(* Types (for readability)                                                *)
(***************************************************************************)
Message == 
    [type : {"Query", "Reply", "Terminate"},
     src  : SlushLoopProcess ∪ SlushQueryProcess,
     dst  : SlushLoopProcess ∪ SlushQueryProcess,
     payload : ("color" : (Colors ∪ {NoColor}))]

PcLabel == {"ClientAssign", "LoopWaitColor", "LoopSample", "LoopWaitReplies",
            "LoopDone", 
            "QueryLoop", "QueryDone"}

\* Helper to find the node that a process hosts
HostNode(p) == 
    CHOOSE n \in Node : <<p, "Loop", n>> \in HostMapping
    \cup 
    CHOOSE n \in Node : <<p, "Query", n>> \in HostMapping

\* Helper to determine whether a proc is a loop or query proc
IsLoop(p) == p \in SlushLoopProcess
IsQuery(p) == p \in SlushQueryProcess

(***************************************************************************)
(* Initial state                                                          *)
(***************************************************************************)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"Client"} |-> 
                 IF p = "Client" THEN "ClientAssign"
                 ELSE IF p \in SlushLoopProcess THEN "LoopWaitColor"
                 ELSE "QueryLoop"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

(***************************************************************************)
(* Actions                                                                *)
(***************************************************************************)

(* 1. Client assigns a random color to an uncolored node *)
ClientAssign ==
    /\ pc["Client"] = "ClientAssign"
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ LET col == CHOOSE c \in Colors : TRUE IN
                /\ color' = [color EXCEPT ![n] = col]
                /\ pc' = [pc EXCEPT !["Client"] = "ClientAssign"]
                /\ UNCHANGED <<msgs, sample, iter>>
    /\ \A n \in Node : color[n] # NoColor => 
          /\ pc' = [pc EXCEPT !["Client"] = "ClientAssign"]
          /\ UNCHANGED <<color, msgs, sample, iter>>

(* 2. Loop process waits until its node is colored *)
LoopWaitColor(lp) ==
    /\ pc[lp] = "LoopWaitColor"
    /\ LET n == HostNode(lp) IN
          /\ color[n] # NoColor
          /\ pc' = [pc EXCEPT ![lp] = "LoopSample"]
          /\ UNCHANGED <<color, msgs, sample, iter>>

(* 3. Loop process creates a sample set and sends queries *)
LoopSample(lp) ==
    /\ pc[lp] = "LoopSample"
    /\ iter[lp] < SlushIterationCount
    /\ LET n == HostNode(lp) IN
          /\ sample[lp] = {}
          /\ \E s \in SUBSET (Node \ {n}) :
                 /\ Cardinality(s) = SampleSetSize
                 /\ \A peer \in s :
                       LET qp == CHOOSE qp \in SlushQueryProcess :
                               HostNode(qp) = peer IN
                       msgs' = msgs \cup {
                           [type |-> "Query",
                            src  |-> lp,
                            dst  |-> qp,
                            payload |-> [color |-> color[n]]]
                       }
                 /\ sample' = [sample EXCEPT ![lp] = s]
                 /\ pc' = [pc EXCEPT ![lp] = "LoopWaitReplies"]
                 /\ UNCHANGED <<color, iter>>
          /\ UNCHANGED <<color, iter>>

(* 4. Query process replies (adopting color if uncolored) *)
QueryReply(qp) ==
    /\ pc[qp] = "QueryLoop"
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst = qp
          /\ LET n == HostNode(qp) IN
                /\ IF color[n] = NoColor
                      THEN color' = [color EXCEPT ![n] = m.payload.color]
                      ELSE UNCHANGED color
                /\ msgs' = msgs \ {m} \cup {
                     [type |-> "Reply",
                      src  |-> qp,
                      dst  |-> m.src,
                      payload |-> [color |-> color'[n]]]
                 }
                /\ pc' = pc
                /\ UNCHANGED <<sample, iter>>

(* 5. Loop process tallies replies and possibly flips its node's color *)
LoopTally(lp) ==
    /\ pc[lp] = "LoopWaitReplies"
    /\ LET n == HostNode(lp) IN
          /\ \E replies \in SUBSET msgs :
                 /\ \A r \in replies :
                        /\ r.type = "Reply"
                        /\ r.dst = lp
                 /\ Cardinality(replies) = SampleSetSize
                 /\ LET redCnt == Cardinality({r \in replies : r.payload.color = "Red"}) IN
                    blueCnt == Cardinality({r \in replies : r.payload.color = "Blue"}) IN
                 /\ IF redCnt >= PickFlipThreshold
                        THEN color' = [color EXCEPT ![n] = "Red"]
                 /\ ELSE IF blueCnt >= PickFlipThreshold
                        THEN color' = [color EXCEPT ![n] = "Blue"]
                 /\ ELSE color' = color
                 /\ msgs' = msgs \ replies
                 /\ sample' = [sample EXCEPT ![lp] = {}]
                 /\ iter' = [iter EXCEPT ![lp] = iter[lp] + 1]
                 /\ IF iter' [lp] = SlushIterationCount
                        THEN pc' = [pc EXCEPT ![lp] = "LoopDone"]
                        ELSE pc' = [pc EXCEPT ![lp] = "LoopSample"]
                 /\ UNCHANGED <<pc>>

(* 6. Loop process termination broadcast *)
LoopTerminate(lp) ==
    /\ pc[lp] = "LoopDone"
    /\ msgs' = msgs \cup { [type |-> "Terminate",
                           src  |-> lp,
                           dst  |-> "Client",
                           payload |-> [color |-> NoColor]] }
    /\ pc' = [pc EXCEPT ![lp] = "LoopDone"]
    /\ UNCHANGED <<color, sample, iter>>

(* 7. Query process exits when all loop processes have terminated *)
QueryDone(qp) ==
    /\ pc[qp] = "QueryLoop"
    /\ \A lp \in SlushLoopProcess : pc[lp] = "LoopDone"
    /\ pc' = [pc EXCEPT ![qp] = "QueryDone"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : LoopWaitColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopSample(lp)
    \/ \E qp \in SlushQueryProcess : QueryReply(qp)
    \/ \E lp \in SlushLoopProcess : LoopTally(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryDone(qp)

(***************************************************************************)
(* Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

(***************************************************************************)
(* Invariant                                                               *)
(***************************************************************************)
TypeInvariant ==
    /\ \A n \in Node : color[n] \in Colors \cup {NoColor}
    /\ \A m \in msgs :
          /\ m.type \in {"Query", "Reply", "Terminate"}
          /\ m.src  \in SlushLoopProcess \cup SlushQueryProcess
          /\ m.dst  \in SlushLoopProcess \cup SlushQueryProcess
          /\ IF m.type = "Query" 
                THEN m.payload.color \in Colors
                ELSE IF m.type = "Reply"
                     THEN m.payload.color \in Colors \cup {NoColor}
                     ELSE m.payload = [color |-> NoColor]

=============================================================================