---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

(* ---------- CONSTANTS ---------- *)
CONSTANT Node
CONSTANT SlushLoopProcess
CONSTANT SlushQueryProcess
CONSTANT HostMapping
CONSTANT SlushIterationCount
CONSTANT SampleSetSize
CONSTANT PickFlipThreshold
CONSTANT NoColor
CONSTANT NoMessage

(* ---------- Derived sets ---------- *)
Colors == {"Red", "Blue"}

ColorsOrNone == Colors \cup {NoColor}

Proc == SlushLoopProcess \cup SlushQueryProcess

MsgType == {"Query", "Reply", "Term"}

(* ---------- Types ---------- *)
NodeSet == Node
LoopSet == SlushLoopProcess
QuerySet == SlushQueryProcess
AllProcs == Proc

(* ---------- State variables ---------- *)
VARIABLES
    color,          \* [node -> ColorsOrNone]
    msgs,           \* set of messages
    pc,             \* [process -> pcLabel]
    sample,         \* [loopProc -> SUBSET Node]
    iter            \* [loopProc -> Nat]

vars == <<color, msgs, pc, sample, iter>>

(* ---------- Message definition ---------- *)
Message == [type : MsgType,
            from : Proc,
            to   : Proc,
            payload : UNION {Colors, NoMessage}]

(* ---------- Helper definitions ---------- *)
LoopOf(p) ==
    IF p \in LoopSet THEN p
    ELSE IF p \in QuerySet THEN
        CHOOSE l \in LoopSet : [l, p] \in HostMapping
    ELSE NoMessage

QueryOf(p) ==
    IF p \in QuerySet THEN p
    ELSE IF p \in LoopSet THEN
        CHOOSE q \in QuerySet : [p, q] \in HostMapping
    ELSE NoMessage

HostNode(p) ==
    IF p \in LoopSet THEN
        CHOOSE n \in NodeSet : [n, p] \in HostMapping
    ELSE IF p \in QuerySet THEN
        CHOOSE n \in NodeSet : [n, p] \in HostMapping
    ELSE NoMessage

(* ---------- Initial state ---------- *)
Init ==
    /\ color = [n \in NodeSet |-> NoColor]
    /\ msgs   = {}
    /\ pc     = [proc \in AllProcs |-> "Start"]
    /\ sample = [lp \in LoopSet |-> {}]
    /\ iter   = [lp \in LoopSet |-> 0]

(* ---------- Actions ---------- *)

(* 1. Client assigns a color to an uncolored node *)
ClientAssign ==
    /\ pc[ "Client" ] = "Start"
    /\ \E n \in NodeSet:
          /\ color[n] = NoColor
          /\ LET c == CHOOSE col \in Colors : TRUE IN
                /\ color' = [color EXCEPT ![n] = c]
                /\ pc'    = [pc EXCEPT !["Client"] = "Start"]
                /\ UNCHANGED <<msgs, sample, iter>>
    \/ /\ pc[ "Client" ] = "Start"
       /\ \A n \in NodeSet: color[n] # NoColor
       /\ pc' = [pc EXCEPT !["Client"] = "Done"]
       /\ UNCHANGED <<color, msgs, sample, iter>>

(* 2. Loop process waits until its host node has a color *)
RequireColor(lp) ==
    /\ pc[lp] = "WaitColor"
    /\ \E c \in Colors:
          /\ color[HostNode(lp)] = c
          /\ pc' = [pc EXCEPT ![lp] = "Sample"]
          /\ UNCHANGED <<color, msgs, sample, iter>>
    \/ /\ pc[lp] = "WaitColor"
       /\ color[HostNode(lp)] = NoColor
       /\ UNCHANGED vars

(* 3. Loop process selects a sample and sends queries *)
QuerySample(lp) ==
    /\ pc[lp] = "Sample"
    /\ SampleSetSize <= Cardinality(NodeSet) - 1
    /\ \E s \in SUBSET (NodeSet \ {HostNode(lp)}):
          /\ Cardinality(s) = SampleSetSize
          /\ LET newMsgs == { [type |-> "Query",
                               from |-> lp,
                               to   |-> QueryOf(q),
                               payload |-> color[HostNode(lp)] ] :
                               q \in s }
          /\ msgs'   = msgs \cup newMsgs
          /\ sample' = [sample EXCEPT ![lp] = s]
          /\ pc'     = [pc EXCEPT ![lp] = "Collect"]
          /\ UNCHANGED <<color, iter>>
    \/ /\ pc[lp] = "Sample"
       /\ UNCHANGED vars

(* 4. Query process responds to a query *)
RespondQuery(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.to   = qp
          /\ LET n == HostNode(qp) IN
                /\ IF color[n] = NoColor
                      THEN color' = [color EXCEPT ![n] = m.payload]
                      ELSE color' = color
                /\ LET reply == [type |-> "Reply",
                                 from |-> qp,
                                 to   |-> m.from,
                                 payload |-> color[n]] IN
                     msgs' = (msgs \ {m}) \cup {reply}
                /\ UNCHANGED <<sample, iter, pc>>
    \/ /\ pc[qp] = "ReplyLoop"
       /\ UNCHANGED vars

(* 5. Loop process tallies replies and possibly flips color *)
TallyReplies(lp) ==
    /\ pc[lp] = "Collect"
    /\ LET s == sample[lp] IN
       /\ \A n \in s :
            \E r \in msgs :
               /\ r.type = "Reply"
               /\ r.from = QueryOf(n)
               /\ r.to   = lp
       /\ LET replies == { r.payload :
                           \E n \in s :
                               \E r \in msgs :
                                   /\ r.type = "Reply"
                                   /\ r.from = QueryOf(n)
                                   /\ r.to   = lp } IN
          LET cnt(c) == Cardinality({ x \in replies : x = c }) IN
          /\ IF cnt(PickOneColor) >= PickFlipThreshold
                THEN color' = [color EXCEPT ![HostNode(lp)] = PickOneColor]
                ELSE color' = color
          /\ msgs'   = { m \in msgs :
                           ~(
                             /\ m.type = "Reply"
                             /\ m.to   = lp
                             /\ m.from \in { QueryOf(n) : n \in s }
                           ) }
          /\ iter'   = [iter EXCEPT ![lp] = iter[lp] + 1]
          /\ IF iter[lp] + 1 >= SlushIterationCount
                THEN pc' = [pc EXCEPT ![lp] = "Terminate"]
                ELSE pc' = [pc EXCEPT ![lp] = "Sample"]
          /\ sample' = [sample EXCEPT ![lp] = {}]
          /\ UNCHANGED <<pc>>
    \/ /\ pc[lp] = "Collect"
       /\ UNCHANGED vars
WHERE
  PickOneColor == 
    IF cnt("Red") >= PickFlipThreshold THEN "Red"
    ELSE IF cnt("Blue") >= PickFlipThreshold THEN "Blue"
    ELSE "Red" \* tie‑break arbitrarily

(* 6. Loop termination broadcast *)
Terminate(lp) ==
    /\ pc[lp] = "Terminate"
    /\ msgs' = msgs \cup { [type |-> "Term",
                            from |-> lp,
                            to   |-> "AllLoops",
                            payload |-> NoMessage] }
    /\ pc'   = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sample, iter>>

(* 7. Query processes exit when all loops are done *)
QueryExit(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \A lp \in LoopSet : pc[lp] = "Done"
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(* ---------- Next-state relation ---------- *)
Next ==
    \/ \E lp \in LoopSet: RequireColor(lp)
    \/ \E lp \in LoopSet: QuerySample(lp)
    \/ \E lp \in LoopSet: TallyReplies(lp)
    \/ \E lp \in LoopSet: Terminate(lp)
    \/ \E qp \in QuerySet: RespondQuery(qp)
    \/ \E qp \in QuerySet: QueryExit(qp)
    \/ ClientAssign

(* ---------- Specification ---------- *)
Spec == Init /\ [][Next]_vars

(* ---------- Safety invariant ---------- *)
TypeInvariant ==
    /\ \A n \in NodeSet : color[n] \in ColorsOrNone
    /\ \A m \in msgs :
          /\ m.type \in MsgType
          /\ m.from \in AllProcs
          /\ m.to   \in AllProcs
          /\ (m.type = "Query"  => m.payload \in Colors)
          /\ (m.type = "Reply"  => m.payload \in ColorsOrNone)
          /\ (m.type = "Term"   => m.payload = NoMessage)

=============================================================================