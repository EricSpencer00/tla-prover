---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A host mapping ties each node to the loop and query process that act on it.
Associated(n, p) == << n, p[1], p[2] >> \in HostMapping

\* Messages are sent over an unordered network, so the in-flight set is free to
\* reorder; a loop process ties each reply it receives back to the peer it queried.
Message == [mtype: {"query", "reply", "term"}, from: Node, to: Node,
             seq: 0 .. SlushIterationCount, col: {NoColor, "red", "blue"}]

RECURSIVE Count(_, _)
Count(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Count(f, S \ {x})

VARIABLES nodeColor, messages, pc, sample, iters

vars == << nodeColor, messages, pc, sample, iters >>

Bump(n) == IF n < SlushIterationCount THEN n + 1 ELSE n

TypeOK ==
  /\ nodeColor \in [Node -> {NoColor, "red", "blue"}]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"nocolor", "waiting", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iters \in [SlushLoopProcess -> 0 .. SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess |-> "nocolor"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

AssignColor(n) ==
  /\ nodeColor[n] = NoColor
  /\ \E c \in {"red", "blue"} : nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ UNCHANGED << messages, pc, sample, iters >>

LaunchLoop(p, n) ==
  /\ pc[p] = "nocolor"
  /\ Associated(n, << SlushLoopProcess, SlushQueryProcess >>)
  /\ nodeColor[n] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED << nodeColor, messages, sample, iters >>

QueryPeers(p, n) ==
  /\ pc[p] = "waiting"
  /\ iters[p] < SlushIterationCount
  /\ \E S \in SUBSET (Node \ {n}) :
       /\ Cardinality(S) = SampleSetSize
       /\ sample' = [sample EXCEPT ![p] = S]
       /\ messages' = messages \cup
            {[mtype |-> "query", from |-> n, to |-> q,
              seq |-> iters[p], col |-> nodeColor[n]] : q \in S}
  /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED << nodeColor, iters >>

AdoptUncolored(m) ==
  /\ m.col # NoColor
  /\ nodeColor[m.to] = NoColor
  /\ nodeColor' = [nodeColor EXCEPT ![m.to] = m.col]
  /\ UNCHANGED << messages, pc, sample, iters >>

ReplyQuery(m) ==
  /\ m.mtype = "query"
  /\ m.col # NoColor
  /\ messages' = (messages \ {m}) \cup
       {[mtype |-> "reply", from |-> m.to, to |-> m.from,
         seq |-> m.seq, col |-> nodeColor[m.to]]}
  /\ UNCHANGED << nodeColor, pc, sample, iters >>

\* The flip only fires once a strict majority of the sampled replies agree.
FlipAdopt(p, n, m) ==
  /\ m.mtype = "reply"
  /\ pc[p] = "tallying"
  /\ m.seq = iters[p]
  /\ m.from = n
  /\ nodeColor[n] = m.col
  /\ Count([q \in sample[p] |-> IF \E r \in messages :
           /\ r.mtype = "reply" /\ r.seq = iters[p]
           /\ r.from = q /\ r.col = m.col
           THEN 1 ELSE 0],
      sample[p]) >= PickFlipThreshold
  /\ nodeColor' = [nodeColor EXCEPT ![n] = m.col]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iters' = [iters EXCEPT ![p] = Bump(iters[p])]
  /\ messages' = messages \ {m}

ObserveReply(m) ==
  /\ m.mtype = "reply"
  /\ pc[CHOOSE p \in SlushLoopProcess : m.seq = iters[p]] = "sampling"
  /\ pc' = [pc EXCEPT ![CHOOSE p \in SlushLoopProcess : m.seq = iters[p]] = "tallying"]
  /\ UNCHANGED << nodeColor, messages, sample, iters >>

LoopDone(p) ==
  /\ pc[p] = "done"
  /\ iters[p] = SlushIterationCount
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED << nodeColor, messages, sample, iters >>

BroadcastTerm(p, n) ==
  /\ pc[p] = "waiting"
  /\ iters[p] = SlushIterationCount
  /\ messages' = messages \cup
       {[mtype |-> "term", from |-> n, to |-> NoMessage,
         seq |-> 0, col |-> NoColor]}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << nodeColor, sample, iters >>

QueryLoopExit ==
  /\ \A q \in SlushQueryProcess :
       (pc[CHOOSE p \in SlushLoopProcess : Associated(q, << p, q >>)] = "done")
         => pc[q] = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Node : AssignColor(n)
  \/ \E p \in SlushLoopProcess, n \in Node : LaunchLoop(p, n)
  \/ \E p \in SlushLoopProcess, n \in Node : QueryPeers(p, n)
  \/ \E m \in messages : AdoptUncolored(m)
  \/ \E m \in messages : ReplyQuery(m)
  \/ \E p \in SlushLoopProcess, n \in Node, m \in messages : FlipAdopt(p, n, m)
  \/ \E m \in messages : ObserveReply(m)
  \/ \E p \in SlushLoopProcess : LoopDone(p)
  \/ \E p \in SlushLoopProcess, n \in Node : BroadcastTerm(p, n)
  \/ QueryLoopExit

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

AllProcessesDone == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done")

====