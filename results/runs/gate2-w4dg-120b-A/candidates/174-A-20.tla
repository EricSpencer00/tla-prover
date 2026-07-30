---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

\* SlushLoopProcess: the per-node loop drivers. SlushQueryProcess: the per-node
\* responders to incoming query messages. HostMapping ties each node to its
\* loop and query process (a set of triples). NoColor and NoMessage are sentinel
\* values for uncolored nodes and messages that are not in use.

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(SlushQueryProcess) = Cardinality(Node)
       /\ HostMapping \subseteq (Node \X SlushLoopProcess \X SlushQueryProcess)

Messages == [to : SlushLoopProcess, kind : {"Query", "Reply", "Terminate"}]
            \cup [to : SlushQueryProcess, kind : {"QueryResp"}]

Clients == SlushQueryProcess \union SlushLoopProcess

VARIABLES color, msgs, pc, sample, iterations

vars == <<color, msgs, pc, sample, iterations>>

ProcessOf(lp) == CHOOSE n \in Node : \E qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping
ResponderOf(qp) == CHOOSE n \in Node : \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in Clients |-> "idle"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iterations = [lp \in SlushLoopProcess |-> 0]

ClientAssignColor ==
    /\ \E n \in Node : color[n] = NoColor
       /\ \E c \in {0, 1} : color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pc, sample, iterations>>

RequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "idle"
         /\ color[ProcessOf(lp)] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = "ready"]
    /\ UNCHANGED <<color, msgs, sample, iterations>>

QuerySampleSet ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "ready"
         /\ sample' = [sample EXCEPT ![lp] = {ResponderOf(qp) : qp \in SlushQueryProcess}]
         /\ msgs' = msgs \union
             {[to |-> qp, kind |-> "Query"] : qp \in SlushQueryProcess}
         /\ pc' = [pc EXCEPT ![lp] = "waiting"]
    /\ UNCHANGED <<color, iterations>>

RespondToQuery ==
    /\ \E qp \in SlushQueryProcess :
         /\ \E m \in msgs : m.kind = "Query" /\ m.to = qp
         /\ color[ResponderOf(qp)] = NoColor
         /\ color' = [color EXCEPT ![ResponderOf(qp)] = color[ProcessOf(m.to)]]
         /\ msgs' = (msgs \ {m}) \union
             {[to |-> ProcessOf(m.to), kind |-> "Reply"]}
    /\ UNCHANGED <<pc, sample, iterations>>

ReplyTally ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "waiting"
         /\ \A qp \in sample[lp] : \E m \in msgs : m.kind = "Reply" /\ m.to = lp
         /\ LET votes == {color[ResponderOf(qp)] : qp \in sample[lp]}
                maxc == Cardinality({v \in votes : v = 1})
                maxn == Cardinality({v \in votes : v = 0})
                agg == IF maxc >= maxn THEN 1 ELSE 0
                flip == IF Cardinality(votes) >= SampleSetSize /\ agg >= PickFlipThreshold
                          THEN agg ELSE color[ProcessOf(lp)]
            IN color' = [color EXCEPT ![ProcessOf(lp)] = flip]
         /\ sample' = [sample EXCEPT ![lp] = {}]
         /\ iterations' = [iterations EXCEPT ![lp] = @ + 1]
         /\ pc' = [pc EXCEPT ![lp] = "ready"]
    /\ UNCHANGED msgs

LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "ready"
         /\ iterations[lp] < SlushIterationCount
         /\ pc' = [pc EXCEPT ![lp] = "finished"]
         /\ msgs' = msgs \union {[to |-> lp, kind |-> "Terminate"]}
    /\ UNCHANGED <<color, sample, iterations>>

QueryLoopExit ==
    /\ \E qp \in SlushQueryProcess :
         /\ pc[qp] = "idle"
         /\ \A lp \in SlushLoopProcess : [to |-> lp, kind |-> "Terminate"] \in msgs
         /\ pc' = [pc EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<color, msgs, sample, iterations>>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ ReplyTally \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssignColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(ReplyTally)

TypeInvariant ==
    /\ color \in [Node -> {0, 1, NoColor}]
    /\ msgs \subseteq Messages
    /\ pc \in [Clients -> {"idle", "ready", "waiting", "finished", "done"}]

====