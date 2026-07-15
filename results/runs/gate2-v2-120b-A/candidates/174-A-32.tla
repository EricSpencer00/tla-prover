---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Constants (to be supplied in a .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS
    Node,               \* Set of all node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples <<proc, proc, node>> linking hosts
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Size of the peer sample each loop process selects
    PickFlipThreshold,  \* Minimum number of matching replies to trigger a flip
    NoColor,            \* Special value representing "uncolored"
    NoMessage           \* Special value representing "no message"

(* ----------------------------------------------------------------------
   Derived definitions
   ---------------------------------------------------------------------- *)

\* The two possible colors of the protocol
Colors == {"Red", "Blue"}

\* The set of all allowed colors together with the uncolored marker
AllColors == Colors \cup {NoColor}

\* Helper to obtain the node associated with a loop or query process via HostMapping
NodeOf(proc) == 
    IF proc \in SlushLoopProcess \cup SlushQueryProcess THEN
        CHOOSE n \in Node : <<proc, _, n>> \in HostMapping
    ELSE NoColor

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)

VARIABLES
    color,          \* [node -> color] mapping, values in AllColors
    msgs,           \* Set of in‑flight messages
    pc,             \* [proc -> program counter label]
    sample,         \* [loopProc -> SUBSET Node] the current peer sample
    iterCnt         \* [loopProc -> Nat] number of completed iterations

(* ----------------------------------------------------------------------
   Message definition
   ---------------------------------------------------------------------- *)

Msg == [type : {"Query", "Reply", "Terminate"},
        src  : Proc,
        dst  : Proc,
        payload : UNION {Colors, NoColor, NULL}]

Proc == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in Proc |-> 
            CASE p \in SlushLoopProcess   -> "waitColor"
               [] p \in SlushQueryProcess  -> "replyLoop"
               [] p = "Client"             -> "assign"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iterCnt = [lp \in SlushLoopProcess |-> 0]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

ClientAssignColor ==
    /\ pc["Client"] = "assign"
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ LET c == CHOOSE col \in Colors : TRUE IN
                 /\ color' = [color EXCEPT ![n] = c]
                 /\ UNCHANGED << msgs, pc, sample, iterCnt >>
                 /\ pc' = [pc EXCEPT !["Client"] = "assign"]
    \/ /\ \A n \in Node : color[n] # NoColor
         /\ pc' = [pc EXCEPT !["Client"] = "done"]
         /\ UNCHANGED << color, msgs, sample, iterCnt >>

RequireColor(loop) ==
    /\ loop \in SlushLoopProcess
    /\ pc[loop] = "waitColor"
    /\ color[NodeOf(loop)] # NoColor
    /\ pc' = [pc EXCEPT ![loop] = "sample"]
    /\ UNCHANGED << color, msgs, sample, iterCnt >>

QuerySample(loop) ==
    /\ loop \in SlushLoopProcess
    /\ pc[loop] = "sample"
    /\ iterCnt[loop] < SlushIterationCount
    /\ sample' = [sample EXCEPT ![loop] = 
          CHOOSE s \in SUBSET (Node \ {NodeOf(loop)}) : Cardinality(s) = SampleSetSize]
    /\ msgs' = msgs \cup {
          [type |-> "Query",
           src  |-> loop,
           dst  |-> qproc,
           payload |-> color[NodeOf(loop)]]
          : qproc \in SlushQueryProcess :
                NodeOf(qproc) \in sample[loop]
        }
    /\ pc' = [pc EXCEPT ![loop] = "waitReplies"]
    /\ UNCHANGED << color, iterCnt >>

RespondToQuery ==
    /\ \E qproc \in SlushQueryProcess :
          /\ \E m \in msgs :
                /\ m.type = "Query"
                /\ m.dst = qproc
                /\ LET n == NodeOf(qproc) IN
                       /\ IF color[n] = NoColor THEN 
                              color' = [color EXCEPT ![n] = m.payload]
                          ELSE UNCHANGED color
                /\ msgs' = (msgs \ {m}) \cup {
                       [type |-> "Reply",
                        src  |-> qproc,
                        dst  |-> m.src,
                        payload |-> color[n]]
                   }
                /\ pc' = [pc EXCEPT ![qproc] = "replyLoop"]
    /\ UNCHANGED << sample, iterCnt >>

TallyReplies(loop) ==
    /\ loop \in SlushLoopProcess
    /\ pc[loop] = "waitReplies"
    /\ \A qproc \in SlushQueryProcess :
          (NodeOf(qproc) \in sample[loop]) =>
              \E m \in msgs :
                  /\ m.type = "Reply"
                  /\ m.dst = loop
                  /\ m.src = qproc
    /\ LET replies == { m.payload :
            \E qproc \in SlushQueryProcess :
                (NodeOf(qproc) \in sample[loop]) /\ 
                m \in msgs /\ 
                m.type = "Reply" /\ 
                m.dst = loop /\ 
                m.src = qproc }
         redCnt == Cardinality({c \in replies : c = "Red"})
         blueCnt == Cardinality({c \in replies : c = "Blue"})
         maxCnt == Max({redCnt, blueCnt})
         newColor == 
            IF maxCnt >= PickFlipThreshold THEN
                IF redCnt >= blueCnt THEN "Red" ELSE "Blue"
            ELSE color[NodeOf(loop)]
    IN
    /\ color' = [color EXCEPT ![NodeOf(loop)] = newColor]
    /\ msgs' = msgs \ { m \in msgs : 
            m.type = "Reply" /\ m.dst = loop /\ NodeOf(m.src) \in sample[loop] }
    /\ sample' = [sample EXCEPT ![loop] = {}]
    /\ iterCnt' = [iterCnt EXCEPT ![loop] = @ + 1]
    /\ pc' = [pc EXCEPT ![loop] = 
                IF iterCnt[loop] + 1 = SlushIterationCount THEN "terminate"
                ELSE "sample"]
    /\ UNCHANGED << pc, msgs, sample, iterCnt, color >>

TerminateLoop(loop) ==
    /\ loop \in SlushLoopProcess
    /\ pc[loop] = "terminate"
    /\ msgs' = msgs \cup {
          [type |-> "Terminate",
           src  |-> loop,
           dst  |-> "Client",
           payload |-> NULL]
        }
    /\ pc' = [pc EXCEPT ![loop] = "done"]
    /\ UNCHANGED << color, sample, iterCnt, msgs >>

QueryLoopExit ==
    /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
    /\ \A qp \in SlushQueryProcess :
          pc[qp] # "replyLoop"   \* they have left the reply loop
    /\ UNCHANGED << color, msgs, pc, sample, iterCnt >>

DoneLoop(lp) ==
    /\ lp \in SlushLoopProcess
    /\ pc[lp] = "done"
    /\ UNCHANGED << color, msgs, pc, sample, iterCnt >>

DoneClient ==
    /\ pc["Client"] = "done"
    /\ UNCHANGED << color, msgs, pc, sample, iterCnt >>

Next ==
    \/ ClientAssignColor
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : QuerySample(lp)
    \/ RespondToQuery
    \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
    \/ \E lp \in SlushLoopProcess : TerminateLoop(lp)
    \/ QueryLoopExit
    \/ \E lp \in SlushLoopProcess : DoneLoop(lp)
    \/ DoneClient

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iterCnt>>

(* ----------------------------------------------------------------------
   Type invariant (the only invariant required by the configuration)
   ---------------------------------------------------------------------- *)

TypeInvariant ==
    /\ color \in [Node -> AllColors]
    /\ msgs \subseteq Msg
    /\ pc \in [Proc -> {"waitColor", "sample", "waitReplies",
                       "terminate", "done", "replyLoop", "assign", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCnt \in [SlushLoopProcess -> Nat]

====