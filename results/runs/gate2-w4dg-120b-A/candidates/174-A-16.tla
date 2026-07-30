---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount,
    SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)

Message == [kind: {"query", "reply", "term"}, to: Node, subj: Node, col: {NoColor} \cup {0, 1}]
ReplyMessage == [kind |-> "reply", to |-> NoMessage, subj |-> NoMessage, col |-> NoColor]

VARIABLES color, msgs, looppc, querypc, sample, iters

vars == <<color, msgs, looppc, querypc, sample, iters>>

NoSample == [node |-> NoMessage, col |-> NoColor]

TypeInvariant ==
    /\ color \in [Node -> {NoColor} \cup {0, 1}]
    /\ msgs \subseteq Message
    /\ looppc \in [SlushLoopProcess -> {"waiting", "sampling", "tallying", "done"}]
    /\ querypc \in [SlushQueryProcess -> {"replying", "done"}]
    /\ sample \in [SlushLoopProcess -> [node: Node \cup {NoMessage}, col: {NoColor} \cup {0, 1}]]
    /\ iters \in [SlushLoopProcess -> 0 .. SlushIterationCount]

\* The client process is the only one that can assign a color from scratch, and
\* it keeps assigning until every node has a color.
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ looppc = [p \in SlushLoopProcess |-> "waiting"]
    /\ querypc = [q \in SlushQueryProcess |-> "replying"]
    /\ sample = [p \in SlushLoopProcess |-> NoSample]
    /\ iters = [p \in SlushLoopProcess |-> 0]

AssignColor(n) ==
    /\ color[n] = NoColor
    /\ \E c \in {0, 1} : color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, looppc, querypc, sample, iters>>

StartLoop(p) ==
    /\ looppc[p] = "waiting"
    /\ color[HostMapping[p].node] # NoColor
    /\ looppc' = [looppc EXCEPT ![p] = "sampling"]
    /\ UNCHANGED <<color, msgs, querypc, sample, iters>>

\* A deterministic choice of peers is used in place of a random sample.
QueryPeers(p) ==
    /\ looppc[p] = "sampling"
    /\ iters[p] < SlushIterationCount
    /\ Cardinality(msgs) < 4
    /\ \E qs \in {{q \in SlushQueryProcess : q # HostMapping[p].query} : Cardinality(qs) = SampleSetSize} :
        msgs' = msgs \cup {[kind |-> "query", to |-> HostMapping[q].node, subj |-> HostMapping[p].node, col |-> color[HostMapping[p].node]] : q \in qs}
    /\ sample' = [sample EXCEPT ![p] = [node |-> HostMapping[p].node, col |-> color[HostMapping[p].node]]]
    /\ UNCHANGED <<color, looppc, querypc, iters>>

ReplyToQuery(q) ==
    /\ querypc[q] = "replying"
    /\ \E m \in msgs :
        /\ m.kind = "query"
        /\ m.to = HostMapping[q].node
        /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", to |-> m.subj, subj |-> NoMessage,
                col |-> IF color[HostMapping[q].node] = NoColor THEN m.col ELSE color[HostMapping[q].node]]}
    /\ UNCHANGED <<color, looppc, querypc, sample, iters>>

\* The loop process's tally is implicit: it simply waits for every sampled peer's
\* reply to be present, then flips if that reply set is strong enough.
TallyReplies(p) ==
    /\ looppc[p] = "sampling"
    /\ sample[p].node # NoMessage
    /\ \A q \in SlushQueryProcess :
        (HostMapping[q].node \in {m.to : m \in msgs : m.kind = "reply" /\ m.to = sample[p].node})
    /\ Cardinality({m \in msgs : m.kind = "reply" /\ m.to = sample[p].node}) >= SampleSetSize
    /\ LET reds == Cardinality({m \in msgs : m.kind = "reply" /\ m.to = sample[p].node /\ m.col = 0})
           blues == Cardinality({m \in msgs : m.kind = "reply" /\ m.to = sample[p].node /\ m.col = 1})
       IN color' = [color EXCEPT ![HostMapping[p].node] =
            IF reds >= PickFlipThreshold THEN 0
            ELSE IF blues >= PickFlipThreshold THEN 1
            ELSE color[HostMapping[p].node]]
    /\ msgs' = {m \in msgs : m.kind # "reply" \/ m.to # sample[p].node}
    /\ looppc' = [looppc EXCEPT ![p] = "tallying"]
    /\ UNCHANGED <<querypc, sample, iters>>

FinishTally(p) ==
    /\ looppc[p] = "tallying"
    /\ looppc' = [looppc EXCEPT ![p] = "sampling"]
    /\ sample' = [sample EXCEPT ![p] = NoSample]
    /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
    /\ UNCHANGED <<color, msgs, querypc>>

LoopTerminated(p) ==
    /\ looppc[p] \in {"sampling", "tallying"}
    /\ iters[p] = SlushIterationCount
    /\ looppc' = [looppc EXCEPT ![p] = "done"]
    /\ msgs' = msgs \cup {[kind |-> "term", to |-> NoMessage, subj |-> HostMapping[p].node, col |-> NoColor}]
    /\ UNCHANGED <<color, querypc, sample, iters>>

ExitQueryLoop(q) ==
    /\ querypc[q] = "replying"
    /\ \A p \in SlushLoopProcess : looppc[p] = "done"
    /\ querypc' = [querypc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<color, msgs, looppc, sample, iters>>

Next ==
    \/ \E n \in Node : AssignColor(n)
    \/ \E p \in SlushLoopProcess : StartLoop(p)
    \/ \E p \in SlushLoopProcess : QueryPeers(p)
    \/ \E q \in SlushQueryProcess : ReplyToQuery(q)
    \/ \E p \in SlushLoopProcess : TallyReplies(p)
    \/ \E p \in SlushLoopProcess : FinishTally(p)
    \/ \E p \in SlushLoopProcess : LoopTerminated(p)
    \/ \E q \in SlushQueryProcess : ExitQueryLoop(q)

Spec == Init /\ [][Next]_vars

Termination == \A p \in SlushLoopProcess : <>(looppc[p] = "done")

====