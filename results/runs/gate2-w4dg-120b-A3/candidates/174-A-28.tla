---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

MessageType == [kind: {"query", "reply", "done"}, src: Node, dst: Node, col: Node \cup {NoColor}]

VARIABLES
    col, msgs, pc, sample, loops

vars == <<col, msgs, pc, sample, loops>>

\* HostMapping ties each node to its loop process and its query process.
LoopFor(n) == SelectTuple(H, S \in HostMapping : S[1] = n)
QueryFor(n) == SelectTuple(H, S \in HostMapping : S[2] = n)

TypeOK ==
    /\ col \in [Node -> Node \cup {NoColor}]
    /\ msgs \subseteq MessageType
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client_req"} : {"idle", "querying", "tallying", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ loops \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ col = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client_req"}) |-> "idle"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ loops = [lp \in SlushLoopProcess |-> 0]

\* External client assigns random colors; repeats until no uncolored node remains.
AssignColor ==
    /\ pc["client_req"] = "idle"
    /\ \E n \in Node :
         /\ col[n] = NoColor
         /\ \E c \in Node : col' = [col EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pc, sample, loops>>

RequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "idle"
         /\ col[LoopFor(lp)] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = "querying"]
    /\ UNCHANGED <<col, msgs, sample, loops>>

\* Loop process picks a random peer set (modelled as any fixed-size set) and queries it.
QueryPeers ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "querying"
         /\ loops[lp] < SlushIterationCount
         /\ \E Q \in SUBSET Node :
              /\ Q # {}
              /\ Cardinality(Q) = SampleSetSize
              /\ sample' = [sample EXCEPT ![lp] = Q]
              /\ msgs' = msgs \cup {[kind |-> "query", src |-> LoopFor(lp), dst |-> q, col |-> col[LoopFor(lp)]} : q \in Q]
         /\ pc' = [pc EXCEPT ![lp] = "tallying"]
    /\ UNCHANGED <<col, loops>>

\* Respond to an incoming query: uncolored nodes adopt the query's color.
ReplyToQuery ==
    /\ \E qp \in SlushQueryProcess :
         /\ pc[qp] = "idle"
         /\ pc' = [pc EXCEPT ![qp] = "replying"]
    /\ UNCHANGED <<col, msgs, sample, loops>>

\* Any query process with a pending query message replies (adopting if uncolored).
SendReply ==
    /\ \E qp \in SlushQueryProcess :
         /\ \E m \in msgs :
              /\ m.kind = "query"
              /\ m.dst = qp
              /\ col' = IF col[qp] = NoColor THEN [col EXCEPT ![qp] = m.col] ELSE col
              /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", src |-> qp, dst |-> m.src, col |-> col[qp]]}
    /\ UNCHANGED <<pc, sample, loops>>

\* Once all replies for a sampled round are in, the node flips if a color passes the threshold.
TallyReplies ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "tallying"
         /\ \A q \in sample[lp] : \E m \in msgs : m.kind = "reply" /\ m.src = q /\ m.dst = LoopFor(lp)
         /\ Cardinality({q \in sample[lp] : col[q] = NoColor}) = 0
         /\ LET count(c) == Cardinality({q \in sample[lp] : col[q] = c}) IN
              col' = IF \E c \in Node : count(c) >= PickFlipThreshold THEN [col EXCEPT ![LoopFor(lp)] = CHOOSE c \in Node : count(c) >= PickFlipThreshold] ELSE col
         /\ loops' = [loops EXCEPT ![lp] = loops[lp] + 1]
         /\ sample' = [sample EXCEPT ![lp] = {}]
         /\ pc' = [pc EXCEPT ![lp] = "idle"]
         /\ msgs' = {m \in msgs : ~(m.kind = "reply" /\ m.dst = LoopFor(lp))}
    /\ UNCHANGED <<pc, sample, loops>>

TerminateLoop ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "idle"
         /\ loops[lp] = SlushIterationCount
         /\ pc' = [pc EXCEPT ![lp] = "done"]
         /\ msgs' = msgs \cup {[kind |-> "done", src |-> LoopFor(lp), dst |-> LoopFor(lp), col |-> NoColor}]
    /\ UNCHANGED <<col, sample, loops>>

ExitQueryLoop ==
    /\ \E qp \in SlushQueryProcess :
         /\ pc[qp] = "idle"
         /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
         /\ pc' = [pc EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<col, msgs, sample, loops>>

Next ==
    \/ AssignColor \/ RequireColor \/ QueryPeers \/ ReplyToQuery
    \/ SendReply \/ TallyReplies \/ TerminateLoop \/ ExitQueryLoop

Spec == Init /\ [][Next]_vars /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(SendReply)

TypeInvariant == TypeOK

Quiescent ==
    /\ pc["client_req"] = "idle"
    /\ \A n \in Node : col[n] # NoColor
    /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
    /\ \A qp \in SlushQueryProcess : pc[qp] = "done"
    /\ msgs = {}

Termination == <>(Quiescent /\ \A p \in vars : p \in {SlushLoopProcess, SlushQueryProcess, "client_req"})

====