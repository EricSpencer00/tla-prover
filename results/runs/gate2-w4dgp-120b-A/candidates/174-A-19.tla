---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME \A p \in SlushLoopProcess \cup SlushQueryProcess : \E t \in Node : <<p, t>> \in HostMapping

Color == {0, 1, NoColor}

\* Each node hosts exactly one loop-process and one query-process; the host mapping
\* is given as a flat set of triples so both process types can resolve their node.
NodeOf(p) == CHOOSE t \in Node : <<p, t>> \in HostMapping

Square(n) == n * n

\* Message channels: queries from loop to query processes, replies back, and
\* termination notices when a loop process has run out of iterations.
VARIABLES color, msgs, pc, sampleSet, iterations

vars == <<color, msgs, pc, sampleSet, iterations>>

Reply(m) == [kind |-> "queryReply", from |-> m.from, to |-> m.to, payload |-> m.payload]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "start"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterations = [p \in SlushLoopProcess |-> 0]

\* A client request assigns an initial color to some uncolored node -- the only
\* nondeterministic action that injects a value into the network.
ClientAssignColor ==
  /\ pc["client"] = "start"
  /\ \E n \in Node :
       /\ color[n] = NoColor
       /\ \E c \in {0, 1} : color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "done"]
  /\ UNCHANGED <<msgs, sampleSet, iterations>>

RequireColor ==
  /\ pc' = [p \in SlushLoopProcess |-> IF pc[p] = "start" /\ color[NodeOf(p)] # NoColor THEN "awaitingReply" ELSE pc[p]]
  /\ UNCHANGED <<color, msgs, sampleSet, iterations>>

\* Slush's loop samples a random subset of peers and asks them for their color.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "awaitingReply"
       /\ sampleSet[p] = {}
       /\ \E peers \in SUBSET (SlushQueryProcess \ { NodeOf(p) }) :
            /\ Cardinality(peers) = SampleSetSize
            /\ sampleSet' = [sampleSet EXCEPT ![p] = peers]
            /\ msgs' = msgs \cup { [kind |-> "query", from |-> p, to |-> q, payload |-> color[NodeOf(p)]] : q \in peers }
  /\ UNCHANGED <<color, pc, iterations>>

\* A query process replies with its own color; if the node is still uncolored it
\* adopts whatever color the query carries -- a write today that is read tomorrow.
RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.kind = "query"
       /\ LET qproc == m.to
            c == IF color[NodeOf(qproc)] = NoColor THEN m.payload ELSE color[NodeOf(qproc)]
            reply == [kind |-> "queryReply", from |-> qproc, to |-> m.from, payload |-> c] IN
         /\ color' = [color EXCEPT ![NodeOf(qproc)] = (IF color[NodeOf(qproc)] = NoColor THEN c ELSE color[NodeOf(qproc)])]
         /\ msgs' = (msgs \ {m}) \cup {reply}
  /\ UNCHANGED <<pc, sampleSet, iterations>>

\* Once all sampled peers have replied, the loop process may adopt the majority
\* color, provided it meets the flip threshold.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "awaitingReply"
       /\ \E replies \in SUBSET (SlushQueryProcess) :
            /\ replies = { m.from : m \in msgs /\ m.kind = "queryReply" /\ m.to = p }
            /\ replies = sampleSet[p]
            /\ LET count(c) == Cardinality({ q \in replies : color[NodeOf(q)] = c })
                 maxc == CHOOSE c \in {0, 1} : \A d \in {0, 1} : count(c) >= count(d)
                 maxCount == count(maxc) IN
               /\ IF maxCount >= PickFlipThreshold
                    THEN color' = [color EXCEPT ![NodeOf(p)] = maxc]
                    ELSE color' = color
            /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
            /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
            /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ msgs' = { m \in msgs : ~(m.kind = "queryReply" /\ m.to = p) }

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "done"
       /\ iterations[p] >= SlushIterationCount
       /\ msgs' = msgs \cup { [kind |-> "termination", from |-> p, to |-> "broadcast", payload |-> NoMessage] }
       /\ pc' = [pc EXCEPT ![p] = "terminated"]
  /\ UNCHANGED <<color, sampleSet, iterations>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = "terminated"
  /\ pc' = [q \in SlushQueryProcess |-> "done"]
  /\ UNCHANGED <<color, msgs, sampleSet, iterations>>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)

TypeInvariant ==
  /\ color \in [Node -> Color]
  /\ \A m \in msgs : m.kind \in {"query", "queryReply", "termination"}

Termination ==
  /\ \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "done"

====