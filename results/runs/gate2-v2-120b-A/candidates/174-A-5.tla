---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers (one per node)
    SlushQueryProcess,   \* Set of query process identifiers (one per node)
    HostMapping,         \* Set of triples [lp |-> ..., qp |-> ..., nd |-> ...]
    SlushIterationCount, \* Maximum number of iterations each loop process performs
    SampleSetSize,       \* Fixed size of the random peer sample
    PickFlipThreshold,   \* Minimum number of matching replies to cause a flip
    NoColor,             \* Special value representing "uncolored"
    NoMessage            \* Special value representing "no message in flight"

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Colors == { "c1", "c2" } \cup {NoColor}
MsgTypes == {"Query", "Reply", "Terminate"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,          \* [node -> color]
    msgs,           \* Set of messages currently in flight
    pc,             \* [proc -> pc value]   (process program counters)
    sample,         \* [lp -> set of qp]    (sample set held by each loop proc)
    iter            \* [lp -> Nat]          (iterations completed by each loop proc)

\* ----------------------------------------------------------------------
\* Types for safety invariant (not the spec's TypeInvariant)
\* ----------------------------------------------------------------------
NodeColors == [n \in Node |-> Colors]
Msg == [type : {"Query","Reply","Terminate"},
        src  : {SlushLoopProcess, SlushQueryProcess},
        dst  : {SlushLoopProcess, SlushQueryProcess},
        payload : UNION {Colors, {"None"}}]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> "Start"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
HostOfLp(lp) == CHOOSE hm \in HostMapping : hm.lp = lp
HostOfQp(qp) == CHOOSE hm \in HostMapping : hm.qp = qp

OtherLoopProcesses(lp) == SlushLoopProcess \ {lp}
OtherQueryProcesses(lp) == SlushQueryProcess \ {HostOfLp(lp).qp}

\* Returns a deterministic but arbitrary subset of the required size.
SampleSet(lp) ==
    LET candidates == OtherQueryProcesses(lp) IN
    IF Cardinality(candidates) < SampleSetSize
        THEN candidates
        ELSE { x \in candidates : x \in { y \in candidates : y \in SeqToSet(1..SampleSetSize) } }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = "Start"
    /\ \E nd \in Node :
          /\ color[nd] = NoColor
          /\ \E col \in {"c1","c2"} :
                /\ color' = [color EXCEPT ![nd] = col]
                /\ pc' = [pc EXCEPT !["Client"] = "Start"]
                /\ UNCHANGED <<msgs, sample, iter>>
    \/  /\ \A nd \in Node : color[nd] # NoColor
        /\ pc' = [pc EXCEPT !["Client"] = "Done"]
        /\ UNCHANGED <<color, msgs, sample, iter>>

LoopStart ==
    /\ pc[lp] = "Start"
    /\ LET nd == HostOfLp(lp).nd IN
       /\ color[nd] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

LoopSample ==
    /\ pc[lp] = "Sample"
    /\ sample[lp] = {}
    /\ LET nd == HostOfLp(lp).nd
          curCol == color[nd]
          s == SampleSet(lp) IN
       /\ sample' = [sample EXCEPT ![lp] = s]
       /\ msgs' = msgs \cup { [type |-> "Query",
                               src  |-> lp,
                               dst  |-> HostOfLp(lp).qp,
                               payload |-> curCol] : qp \in s }
       /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
    /\ UNCHANGED <<color, iter>>

LoopReceiveReply ==
    /\ pc[lp] = "WaitReplies"
    /\ \E m \in msgs :
          /\ m.type = "Reply"
          /\ m.dst = lp
          /\ LET nd == HostOfLp(lp).nd IN
             /\ color' = [color EXCEPT ![nd] = m.payload]
             /\ msgs' = msgs \ { m }
    /\ UNCHANGED <<sample, iter, pc>>

LoopTallyAndFlip ==
    /\ pc[lp] = "WaitReplies"
    /\ sample[lp] # {}
    /\ \A qp \in sample[lp] :
          \E m \in msgs :
               /\ m.type = "Reply"
               /\ m.dst = lp
               /\ m.src = qp
    /\ LET nd == HostOfLp(lp).nd
           curCol == color[nd]
           replies == { m.payload : m \in msgs /\ m.type = "Reply" /\ m.dst = lp }
           cnt(col) == Cardinality({ r \in replies : r = col }) IN
       /\ (cnt("c1") >= PickFlipThreshold /\ color' = [color EXCEPT ![nd] = "c1"])
          \/ (cnt("c2") >= PickFlipThreshold /\ color' = [color EXCEPT ![nd] = "c2"])
          \/ (color' = color)   \* No flip
       /\ iter' = [iter EXCEPT ![lp] = iter[lp] + 1]
       /\ msgs' = msgs \ { m \in msgs : m.type = "Reply" /\ m.dst = lp }
       /\ pc' = IF iter'[lp] < SlushIterationCount
                 THEN [pc EXCEPT ![lp] = "Sample"]
                 ELSE [pc EXCEPT ![lp] = "Terminate"]
    /\ UNCHANGED sample

LoopTerminate ==
    /\ pc[lp] = "Terminate"
    /\ msgs' = msgs \cup { [type |-> "Terminate",
                            src  |-> lp,
                            dst  |-> "All",
                            payload |-> "None"] }
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sample, iter>>

QueryAwait ==
    /\ pc[qp] = "Start"
    /\ pc' = [pc EXCEPT ![qp] = "Await"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

QueryRespond ==
    /\ pc[qp] = "Await"
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst = qp
          /\ LET nd == HostOfQp(qp).nd
                 qcol == m.payload
                 newColor == IF color[nd] = NoColor THEN qcol ELSE color[nd] IN
             /\ color' = [color EXCEPT ![nd] = newColor]
             /\ msgs' = msgs \ { m } \cup
                        { [type |-> "Reply",
                           src  |-> qp,
                           dst  |-> m.src,
                           payload |-> color'[nd]] }
    /\ UNCHANGED <<sample, iter, pc>>

QueryDoneWhenTerminate ==
    /\ pc[qp] = "Await"
    /\ \A lp \in SlushLoopProcess : pc[lp] = "Done"
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : LoopStart
    \/ \E lp \in SlushLoopProcess : LoopSample
    \/ \E lp \in SlushLoopProcess : LoopReceiveReply
    \/ \E lp \in SlushLoopProcess : LoopTallyAndFlip
    \/ \E lp \in SlushLoopProcess : LoopTerminate
    \/ \E qp \in SlushQueryProcess : QueryAwait
    \/ \E qp \in SlushQueryProcess : QueryRespond
    \/ \E qp \in SlushQueryProcess : QueryDoneWhenTerminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in NodeColors
    /\ msgs \subseteq { [type |-> t,
                         src  |-> s,
                         dst  |-> d,
                         payload |-> p] :
                         t \in MsgTypes,
                         s \in SlushLoopProcess \cup SlushQueryProcess,
                         d \in SlushLoopProcess \cup SlushQueryProcess,
                         p \in (Colors \cup {"None"}) }
    /\ pc \in [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> {"Start","Sample","WaitReplies","Terminate","Done","Await","Start","Done"}]
    /\ sample \in [lp \in SlushLoopProcess |-> SUBSET SlushQueryProcess]
    /\ iter \in [lp \in SlushLoopProcess |-> Nat]

=============================================================================