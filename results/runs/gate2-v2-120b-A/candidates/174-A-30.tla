---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers (one per node)
    SlushQueryProcess,   \* Set of query process identifiers (one per node)
    HostMapping,         \* Set of triples [proc |-> procId, type |-> "loop"/"query", host |-> node]
    SlushIterationCount, \* Max number of iterations each loop process performs
    SampleSetSize,       \* Size of the peer sample each iteration
    PickFlipThreshold,   \* Minimum number of identical replies needed to flip/adopt a color
    NoColor,             \* Special value meaning "uncolored"
    NoMessage            \* Special value meaning "no pending message"

\*-----------------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------------
Color == {"Red", "Blue", NoColor}
MsgType == {"Query", "Reply", "Terminate"}

Message == [type : MsgType,
            src  : SlushLoopProcess \cup SlushQueryProcess,
            dst  : SlushLoopProcess \cup SlushQueryProcess,
            payload : {"Red", "Blue"}]

\*-----------------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------------
VARIABLES
    color,          \* [node -> Color] current color of each node
    msgs,           \* Set of in‑flight messages
    pc,             \* [proc -> pc value] program counter for each process
    sample,         \* [lp -> SUBSET Node] current sampled peers for each loop process
    iterCount       \* [lp -> Nat] number of completed iterations for each loop process

\*-----------------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 
                IF p \in SlushLoopProcess THEN "WaitAssign"
                ELSE IF p \in SlushQueryProcess THEN "ReplyLoop"
                ELSE "Assign"]
    /\ sample    = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]

\*-----------------------------------------------------------------------
\* Process definitions (actions)
\*-----------------------------------------------------------------------

\*--- Client process ----------------------------------------------------
AssignColor ==
    /\ pc["Client"] = "Assign"
    /\ \E n \in Node :
        /\ color[n] = NoColor
        /\ LET col == IF CHOOSE c \in {"Red", "Blue"} : TRUE THEN c ELSE "Red" IN
           /\ color' = [color EXCEPT ![n] = col]
           /\ pc'    = [pc EXCEPT !["Client"] = IF \A m \in Node : color[m] # NoColor
                                             THEN "Done"
                                             ELSE "Assign"]
           /\ UNCHANGED << msgs, sample, iterCount >>

\*--- Loop processes ----------------------------------------------------
RequireColor(lp) ==
    /\ pc[lp] = "WaitAssign"
    /\ \E n \in Node :
        /\ [proc |-> lp, type |-> "loop", host |-> n] \in HostMapping
        /\ color[n] # NoColor
        /\ pc' = [pc EXCEPT ![lp] = "Query"]
        /\ UNCHANGED << color, msgs, sample, iterCount >>

QuerySample(lp) ==
    /\ pc[lp] = "Query"
    /\ \E n \in Node :
        /\ [proc |-> lp, type |-> "loop", host |-> n] \in HostMapping
        /\ sample[lp] = {}               \* only when starting a new round
        /\ \E peers \in SUBSET (Node \ {n}) :
            /\ Cardinality(peers) = SampleSetSize
            /\ LET msgsToSend == { [type |-> "Query", src |-> lp, dst |-> qp, payload |-> color[n]]
                                   : qp \in SlushQueryProcess
                                   : \E t \in HostMapping :
                                         /\ t.type = "query"
                                         /\ t.host \in peers
                                         /\ t.proc = qp } IN
               /\ msgs' = msgs \cup msgsToSend
               /\ sample' = [sample EXCEPT ![lp] = peers]
               /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
               /\ UNCHANGED << color, iterCount >>

WaitReplies(lp) ==
    /\ pc[lp] = "WaitReplies"
    /\ sample[lp] # {}                  \* a round is in progress
    /\ \A qp \in SlushQueryProcess :
          (\E t \in HostMapping :
               t.type = "query"
               /\ t.proc = qp
               /\ t.host \in sample[lp])
          => (\E m \in msgs :
                /\ m.type = "Reply"
                /\ m.dst = lp
                /\ m.src = qp)
    /\ LET replies == { m.payload : m \in msgs
                                   /\ m.type = "Reply"
                                   /\ m.dst = lp
                                   /\ m.src \in SlushQueryProcess
                                   /\ \E t \in HostMapping :
                                         t.type = "query"
                                         /\ t.proc = m.src
                                         /\ t.host \in sample[lp] } IN
       LET redCnt  == Cardinality({c \in replies : c = "Red"})
           blueCnt == Cardinality({c \in replies : c = "Blue"}) IN
       /\ IF redCnt >= PickFlipThreshold
             THEN color' = [color EXCEPT ![n] = "Red"]
          ELSE IF blueCnt >= PickFlipThreshold
             THEN color' = [color EXCEPT ![n] = "Blue"]
          ELSE UNCHANGED color
       /\ msgs' = msgs \ { m \in msgs : m.type = "Reply" /\ m.dst = lp }
       /\ sample'    = [sample EXCEPT ![lp] = {}]
       /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
       /\ pc' = [pc EXCEPT ![lp] = 
                 IF iterCount'[lp] >= SlushIterationCount
                    THEN "Terminate"
                    ELSE "Query"]
       /\ UNCHANGED << >>

Terminate(lp) ==
    /\ pc[lp] = "Terminate"
    /\ LET termMsg == [type |-> "Terminate", src |-> lp, dst |-> lp, payload |-> NoColor] IN
       /\ msgs' = msgs \cup {termMsg}
       /\ pc' = [pc EXCEPT ![lp] = "Done"]
       /\ UNCHANGED << color, sample, iterCount >>

\*--- Query processes ----------------------------------------------------
QueryLoop(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst = qp
          /\ LET n == CHOOSE t \in HostMapping :
                        t.type = "query" /\ t.proc = qp /\ t.host
                 col == m.payload IN
             /\ IF color[n] = NoColor
                   THEN color' = [color EXCEPT ![n] = col]
                   ELSE UNCHANGED color
             /\ LET reply == [type |-> "Reply", src |-> qp, dst |-> m.src, payload |-> color[n]] IN
                /\ msgs' = (msgs \ {m}) \cup {reply}
                /\ UNCHANGED << sample, iterCount, pc >>
    /\ UNCHANGED << >>

\*--- Termination detection for query processes -------------------------
QueryExit(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \A lp \in SlushLoopProcess :
          (\E t \in HostMapping : t.type = "loop" /\ t.proc = lp) =>
            \E m \in msgs :
               /\ m.type = "Terminate"
               /\ m.dst = lp
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED << color, msgs, sample, iterCount >>

\*-----------------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------------
Next ==
    \/ AssignColor
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : QuerySample(lp)
    \/ \E lp \in SlushLoopProcess : WaitReplies(lp)
    \/ \E lp \in SlushLoopProcess : Terminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryLoop(qp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ /\ pc["Client"] = "Done"
       /\ \A p \in (SlushLoopProcess \cup SlushQueryProcess) : pc[p] = "Done"
       /\ UNCHANGED << color, msgs, pc, sample, iterCount >>

\*-----------------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iterCount>>

\*-----------------------------------------------------------------------
\* Type invariant
\*-----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> Color]
    /\ msgs \subseteq Message

\*-----------------------------------------------------------------------
\* THEOREM (optional, can be checked with TLC)
\*-----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====