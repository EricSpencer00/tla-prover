---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A host triple links a node to its loop process and its query process.
Hosts == {h \in HostMapping : h[1] \in Node /\ h[2] \in SlushLoopProcess /\ h[3] \in SlushQueryProcess}
HostsFor(p) == {n \in Node : <<n, p, _>> \in Hosts}

VARIABLES
  color, msgs, pc, sampleSet, loopIter

vars == <<color, msgs, pc, sampleSet, loopIter>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup SlushLoopProcess]
  /\ msgs \subseteq [kind: {NoMessage, "query", "reply", "term"}, from: {NoMessage} \cup (SlushLoopProcess \cup SlushQueryProcess), to: {NoMessage} \cup (SlushLoopProcess \cup SlushQueryProcess), p: SlushLoopProcess, q: SlushQueryProcess, c: SlushLoopProcess \cup SlushQueryProcess \cup {NoColor}]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [x \in SlushLoopProcess \cup SlushQueryProcess |-> IF x \in SlushLoopProcess THEN "waiting" ELSE "reply"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopIter = [p \in SlushLoopProcess |-> 0]

AssignColor(n, c) ==
  /\ color[n] = NoColor
  /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sampleSet, loopIter>>

\* The client refuses to start a node's Slush loop until that node has
\* actually been handed a color by some transaction.
RequireColor(p) ==
  /\ pc[p] = "waiting"
  /\ \E n \in HostsFor(p) : color[n] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "polling"]
  /\ UNCHANGED <<color, msgs, sampleSet, loopIter>>

SendQuery(p, q, n, c) ==
  /\ pc[p] = "polling"
  /\ q \notin sampleSet[p]
  /\ Cardinality(sampleSet[p]) < SampleSetSize
  /\ msgs' = msgs \cup {[kind |-> "query", from |-> p, to |-> q, p |-> p, q |-> q, c |-> c]}
  /\ sampleSet' = [sampleSet EXCEPT ![p] = @ \cup {q}]
  /\ UNCHANGED <<color, pc, loopIter>>

\* Query processes are slow but never fail: they always eventually get to
\* the point where they answer, even if they need to adopt the query's
\* color first in order to stay coherent.
AnswerQuery(m) ==
  /\ pc[m.to] = "reply"
  /\ m.kind = "query"
  /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", from |-> m.to, to |-> m.from, p |-> m.p, q |-> m.q, c |-> IF color[HeadsFor(m.q)] = NoColor THEN m.c ELSE color[HeadsFor(m.q)]]}
  /\ UNCHANGED <<color, pc, sampleSet, loopIter>>

\* Note the per-process tally: the poller only looks at the replies it
\* asked for, so a slow query process only ever reduces its own speed.
TallyAndFlip(p) ==
  /\ pc[p] = "polling"
  /\ \A q \in sampleSet[p] : \E m \in msgs : m.kind = "reply" /\ m.from = q /\ m.p = p
  /\ LET revCount(c) == Cardinality({m \in msgs : m.from \in sampleSet[p] /\ m.p = p /\ m.c = c})
         maxColor == CHOOSE c \in SlushLoopProcess \cup SlushQueryProcess : \A d \in SlushLoopProcess \cup SlushQueryProcess : revCount(c) >= revCount(d)
     IN IF revCount(maxColor) >= PickFlipThreshold
        THEN color' = [color EXCEPT ![HeadsFor(p)] = maxColor]
        ELSE color' = color
  /\ msgs' = {m \in msgs : ~(m.kind = "reply" /\ m.p = p)}
  /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
  /\ loopIter' = [loopIter EXCEPT ![p] = @ + 1]
  /\ pc' = [pc EXCEPT ![p] = IF loopIter[p] + 1 < SlushIterationCount THEN "polling" ELSE "done"]

BroadcastTermination(p) ==
  /\ pc[p] = "done"
  /\ ~(\E m \in msgs : m.kind = "term" /\ m.from = p)
  /\ msgs' = msgs \cup {[kind |-> "term", from |-> p, to |-> NoMessage, p |-> p, q |-> NoMessage, c |-> NoMessage]}
  /\ UNCHANGED <<color, pc, sampleSet, loopIter>>

ExitQueryLoop(q) ==
  /\ pc[q] = "reply"
  /\ \A p \in SlushLoopProcess : \E m \in msgs : m.kind = "term" /\ m.from = p
  /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, msgs, sampleSet, loopIter>>

HeadsFor(q) == CHOOSE n \in Node : <<n, _, q>> \in Hosts

Next ==
  \/ \E n \in Node, c \in SlushLoopProcess : AssignColor(n, c)
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess, q \in SlushQueryProcess, n \in Node, c \in SlushLoopProcess : SendQuery(p, q, n, c)
  \/ \E m \in msgs : AnswerQuery(m)
  \/ \E p \in SlushLoopProcess : TallyAndFlip(p)
  \/ \E p \in SlushLoopProcess : BroadcastTermination(p)
  \/ \E q \in SlushQueryProcess : ExitQueryLoop(q)

Spec == Init /\ [][Next]_vars

\* At most one process ever lingers between steps -- loop processes must
\* answer their polls before they can poll again, which is what forces
\* every node to eventually stop regardless of how slow its peers are.
LivenessQuiescence == (\E x \in SlushLoopProcess \cup SlushQueryProcess : pc[x] # "done") ~> (\A x \in SlushLoopProcess \cup SlushQueryProcess : pc[x] = "done")

====