---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A SlushLoopProcess and a SlushQueryProcess are each hosted by exactly one node; the
\* HostMapping set of triples links them to their host node.
\* The client process (not a separate actor) assigns initial colors to uncolored nodes.

ASSUME Cardinality(Node) = Cardinality(SlushLoopProcess)
Assume == Cardinality(Node) = Cardinality(SlushQueryProcess)
ASSUME SampleSetSize <= Cardinality(Node) - 1

Colors == {"c1", "c2"}
MessageTypes == {"query", "reply", "term"}

VARIABLES nodeColor, msgs, pc, sample, iters

vars == <<nodeColor, msgs, pc, sample, iters>>

TypeOK ==
    /\ nodeColor \in [Node -> Colors \cup {NoColor}]
    /\ msgs \subseteq [dest : Node \cup {NoMessage}, typ : MessageTypes]
    /\ pc \in [SlushLoopProcess -> {"waitColor", "idle", "querying", "tallying", "done"} \cup
                {SlushQueryProcess}] \cup {NoMessage}
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [lp \in SlushLoopProcess |-> "waitColor"] @@
           [qp \in SlushQueryProcess |-> "replying"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iters = [lp \in SlushLoopProcess |-> 0]

\* A query message carries the sender's current color (a snapshot, not a
\* pointer, so the reply is immutable once admitted).
RequestMsg(lp, q) == [dest |-> q, typ |-> "query"]
ReplyMsg(qp, c) == [dest |-> qp, typ |-> "reply"]
TermMsg(lp) == [dest |-> NoMessage, typ |-> "term"]

HostOfLoop(lp) == CHOOSE n \in Node : <<lp, n>> \in HostMapping
HostOfQuery(qp) == CHOOSE n \in Node : <<qp, n>> \in HostMapping

ClientAssignColor ==
    /\ \E n \in Node, c \in Colors :
         /\ nodeColor[n] = NoColor
         /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pc, sample, iters>>

RequireNodeColor(lp) ==
    /\ pc[lp] = "waitColor"
    /\ nodeColor[HostOfLoop(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "idle"]
    /\ UNCHANGED <<nodeColor, msgs, sample, iters>>

QuerySampleSet(lp) ==
    /\ pc[lp] = "idle"
    /\ iters[lp] < SlushIterationCount
    /\ \E Q \in SUBSET Node : Q # {} /\ Cardinality(Q) = SampleSetSize
         /\ sample' = [sample EXCEPT ![lp] = Q]
         /\ msgs' = msgs \cup {[dest |-> q, typ |-> "query"] : q \in Q}
    /\ pc' = [pc EXCEPT ![lp] = "querying"]
    /\ UNCHANGED <<nodeColor, iters>>

RespondToQuery(qp) ==
    /\ pc[qp] \in [SlushQueryProcess -> MessageTypes]
    /\ \E m \in msgs :
         /\ m.dest = qp
         /\ msgs' = msgs \ {m}
         /\ pc' = [pc EXCEPT ![qp] = IF nodeColor[HostOfQuery(qp)] = NoColor
                                         THEN m.typ ELSE pc[qp]]
    /\ msgs' = msgs \cup {ReplyMsg(qp, IF nodeColor[HostOfQuery(qp)] = NoColor THEN m.typ ELSE nodeColor[HostOfQuery(qp)])}
    /\ UNCHANGED <<nodeColor, sample, iters>>

TallyReplies(lp) ==
    /\ pc[lp] = "querying"
    /\ \A q \in sample[lp] : ReplyMsg(q, NoColor) \notin msgs
    /\ LET replyColors == {ReplyMsg(q, NoColor).typ : q \in sample[lp]}
           count(c) == Cardinality({q \in sample[lp] : ReplyMsg(q, NoColor).typ = c})
       IN nodeColor' = [nodeColor EXCEPT ![HostOfLoop(lp)] =
                           IF \E c \in replyColors : count(c) >= PickFlipThreshold THEN
                              CHOOSE c \in replyColors : count(c) >= PickFlipThreshold
                           ELSE nodeColor[HostOfLoop(lp)]]
    /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ iters' = [iters EXCEPT ![lp] = @ + 1]
    /\ pc' = [pc EXCEPT ![lp] = "idle"]
    /\ UNCHANGED msgs

LoopTermination(lp) ==
    /\ pc[lp] = "idle"
    /\ iters[lp] = SlushIterationCount
    /\ pc' = [pc EXCEPT ![lp] = "done"]
    /\ msgs' = msgs \cup {TermMsg(lp)}
    /\ UNCHANGED <<nodeColor, sample, iters>>

QueryLoopExit(qp) ==
    /\ pc[qp] = "replying"
    /\ \A lp \in SlushLoopProcess : TermMsg(lp) \in msgs
    /\ pc' = [pc EXCEPT ![qp] = NoMessage]
    /\ UNCHANGED <<nodeColor, msgs, sample, iters>>

Next ==
    \/ ClientAssignColor
    \/ \E lp \in SlushLoopProcess : RequireNodeColor(lp) \/ QuerySampleSet(lp) \/ TallyReplies(lp) \/ LoopTermination(lp)
    \/ \E qp \in SlushQueryProcess : RespondToQuery(qp) \/ QueryLoopExit(qp)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ClientAssignColor)
    /\ \A lp \in SlushLoopProcess : SF_vars(TallyReplies(lp))
    /\ \A lp \in SlushLoopProcess : WF_vars(LoopTermination(lp))
    /\ \A qp \in SlushQueryProcess : WF_vars(QueryLoopExit(qp))

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] \in {NoMessage, "done"}

====