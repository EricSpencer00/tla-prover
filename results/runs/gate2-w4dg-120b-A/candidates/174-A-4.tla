---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Natural-language description (see prompt): Slush is a metastable voting protocol
\* from the Avalanche whitepaper, rendered here as a deterministic PlusCal spec.
\* It tracks a per-node color, in-flight query/reply messages, per-loop sample
\* sets, and per-loop iteration counts. Color assignment is decided by a
\* quorum of sampled peers.

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

MessageTypes == {"query", "queryReply", "termination"}

VARIABLES
  color, inflight, pc, sample, loopIter

vars == <<color, inflight, pc, sample, loopIter>>

BlankState == [host |-> NoMessage, pc |-> "done", color |-> NoColor]
QueryState == [host |-> NoMessage, pc |-> "replyLoop", color |-> NoColor]
LoopState == [host |-> NoMessage, pc |-> "waitColor", color |-> NoColor]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inflight = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {BlankState.host} |-> BlankState.pc]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopIter = [p \in SlushLoopProcess |-> 0]

\* (1) Client assigns an initial color to an uncolored node.
ClientAssignColor(n, c) ==
  /\ color[n] = NoColor
  /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<inflight, pc, sample, loopIter>>

\* (2) Loop processes wait until their host node has been assigned a color.
RequireColor(lp) ==
  /\ pc[lp] = "waitColor"
  /\ HostMapping[lp].host \in Node
  /\ color[HostMapping[lp].host] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "sample"]
  /\ UNCHANGED <<color, inflight, sample, loopIter>>

\* (3) The loop process samples a random peer subset and sends a query to each.
QuerySampleSet(lp) ==
  /\ pc[lp] = "sample"
  /\ SampleSetSize # 0
  /\ \E peers \in (Node \ {{HostMapping[lp].host}}) : Cardinality(peers) >= SampleSetSize /\ sample' = [sample EXCEPT ![lp] = peers]
  /\ inflight' = [q \in peers |-> [kind |-> "query", to |-> HostMapping[lp].peer, color |-> color[HostMapping[lp].host]]] \cup inflight
  /\ pc' = [pc EXCEPT ![lp] = "tally"]
  /\ UNCHANGED <<color, loopIter>>

\* (4) A query process receives a query: it adopts the color if uncolored,
\* then replies with its current color.
RespondToQuery(qp, m) ==
  /\ m.kind = "query"
  /\ m.to = qp
  /\ HostMapping[qp].host \in Node
  /\ inflight' = (inflight \ {m}) \cup
       [qp |-> [kind |-> "queryReply", to |-> HostMapping[qp].peer, color |-> IF color[HostMapping[qp].host] = NoColor THEN m.color ELSE color[HostMapping[qp].host]]]
  /\ color' = [color EXCEPT ![HostMapping[qp].host] = IF color[HostMapping[qp].host] = NoColor THEN m.color ELSE color[HostMapping[qp].host]]
  /\ UNCHANGED <<pc, sample, loopIter>>

\* (5) The loop process tallies its sampled replies and flips if a color
\* reaches the quorum threshold, then clears its sample.
TallyReplies(lp) ==
  /\ pc[lp] = "tally"
  /\ \E replies \in (SlushQueryProcess \cup {BlankState.host}):
       /\ \A qp \in sample[lp] : [kind |-> "queryReply", to |-> HostMapping[qp].peer, color |-> color[HostMapping[qp].host]] \in replies
       /\ \E col \in {"col1", "col2"} :
            /\ Cardinality({r \in replies : r.color = col}) >= PickFlipThreshold
            /\ HostMapping[lp].host \in Node
            /\ color' = [color EXCEPT ![HostMapping[lp].host] = col]
  /\ sample' = [sample EXCEPT ![lp] = {}]
  /\ loopIter' = [loopIter EXCEPT ![lp] = @ + 1]
  /\ pc' = [pc EXCEPT ![lp] = IF loopIter[lp] + 1 >= SlushIterationCount THEN "terminate" ELSE "sample"]
  /\ UNCHANGED inflight

\* (6) Loop processes broadcast a termination notice once all iterations are done.
Terminate(lp) ==
  /\ pc[lp] = "terminate"
  /\ inflight' = [lp |-> [kind |-> "termination", to |-> HostMapping[lp].peer]] \cup inflight
  /\ pc' = [pc EXCEPT ![lp] = "done"]
  /\ UNCHANGED <<color, sample, loopIter>>

\* (7) Query processes exit once every loop process has terminated.
QueryLoopExit(qp) ==
  /\ pc[qp] = "replyLoop"
  /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
  /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<color, inflight, sample, loopIter>>

AllQuiescent == \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {BlankState.host} : pc[p] = "done"

Next ==
  \/ \E n \in Node, c \in {"col1", "col2"} : ClientAssignColor(n, c)
  \/ \E lp \in SlushLoopProcess : RequireColor(lp) \/ QuerySampleSet(lp) \/ TallyReplies(lp) \/ Terminate(lp)
  \/ \E qp \in SlushQueryProcess, m \in inflight : RespondToQuery(qp, m)
  \/ \E qp \in SlushQueryProcess : QueryLoopExit(qp)
  \/ (\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {BlankState.host} : pc[p] = "done") /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Node, c \in {"col1", "col2"} : ClientAssignColor(n, c))
           /\ WF_vars(\E lp \in SlushLoopProcess : RequireColor(lp))
           /\ WF_vars(\E lp \in SlushLoopProcess : QuerySampleSet(lp))
           /\ WF_vars(\E qp \in SlushQueryProcess, m \in inflight : RespondToQuery(qp, m))
           /\ WF_vars(\E lp \in SlushLoopProcess : TallyReplies(lp))
           /\ WF_vars(\E lp \in SlushLoopProcess : Terminate(lp))
           /\ WF_vars(\E qp \in SlushQueryProcess : QueryLoopExit(qp))

TypeInvariant ==
  /\ color \in [Node -> {"col1", "col2", NoColor}]
  /\ inflight \subseteq [kind : MessageTypes, to : SlushLoopProcess \cup SlushQueryProcess \cup {BlankState.host}, color : {"col1", "col2", NoColor}]
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {BlankState.host} -> {"waitColor", "sample", "tally", "terminate", "replyLoop", "done"}]

Termination == AllQuiescent

====