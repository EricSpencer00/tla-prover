---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Slush is a metastable consensus protocol: each node repeatedly samples a random
\* subset of peers and adopts a sufficiently popular opinion.  Because TLA+ has no
\* probabilistic modeling, this spec is an executable pseudocode version of the
\* protocol, not a statistical analysis of its convergence properties.

\* The color assignment is a partial function: a node may be uncolored (NoColor)
\* until the client process assigns it a color, after which it participates in
\* Slush rounds.  The message set is a bag of query, reply, and termination
\* messages; the loop process's sample set records which peers it queried this
\* round, and its iteration counter tracks how many rounds it has completed.

VARIABLES color, messages, pc, sample, iteration

vars == <<color, messages, pc, sample, iteration>>

Message == [kind: {"query", "reply", "term"}, src: SlushLoopProcess \cup SlushQueryProcess, dst: SlushLoopProcess \cup SlushQueryProcess, payload: {NoColor} \cup (Node \X {0, 1})]

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup (Node \X {0, 1})]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"waiting", "querying", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iteration = [p \in SlushLoopProcess |-> 0]
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> IF p = "client" THEN "querying" ELSE "waiting"]

\* The client process assigns an initial color to an uncolored node.
ClientAssignColor ==
  /\ pc["client"] = "querying"
  /\ \E n \in Node, c \in {0, 1} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = <<n, c>>]
  /\ pc' = [pc EXCEPT !["client"] = "querying"]
  /\ UNCHANGED <<messages, sample, iteration>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waiting"
       /\ \E n \in Node : <<p, n>> \in HostMapping /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "querying"]
  /\ UNCHANGED <<color, messages, sample, iteration>>

\* The loop process samples a random subset of peers and queries them for their
\* current color.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "querying"
       /\ iteration[p] < SlushIterationCount
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Cardinality(Q) = SampleSetSize
            /\ sample' = [sample EXCEPT ![p] = Q]
            /\ messages' = messages \cup {[kind |-> "query", src |-> p, dst |-> q, payload |-> color[CHOOSE n \in Node : <<p, n>> \in HostMapping]] : q \in Q}
  /\ UNCHANGED <<color, pc, iteration>>

\* A query process adopts the query's color if it is still uncolored, then
\* replies with its current color.
RespondToQuery ==
  /\ \E m \in messages :
       /\ m.kind = "query"
       /\ \E n \in Node : <<m.dst, n>> \in HostMapping
       /\ LET cur == IF color[n] = NoColor THEN m.payload ELSE color[n] IN
            /\ color' = [color EXCEPT ![n] = cur]
            /\ messages' = (messages \ {m}) \cup {[kind |-> "reply", src |-> m.dst, dst |-> m.src, payload |-> cur]}
  /\ UNCHANGED <<pc, sample, iteration>>

\* The loop process tallies replies; if one color reaches the flip threshold it
\* adopts that color.  The sample set is cleared and the iteration counter
\* advances.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "querying"
       /\ sample[p] # {}
       /\ \A q \in sample[p] : \E m \in messages : m.kind = "reply" /\ m.src = q /\ m.dst = p
       /\ LET replies == {m.payload : m \in {x \in messages : x.kind = "reply" /\ x.dst = p}} IN
            /\ LET count(c) == Cardinality({x \in replies : x = c}) IN
                 /\ IF \E c \in replies : count(c) >= PickFlipThreshold
                    THEN color' = [color EXCEPT ![CHOOSE n \in Node : <<p, n>> \in HostMapping] = CHOOSE c \in replies : count(c) >= PickFlipThreshold]
                    ELSE color' = color
       /\ messages' = {m \in messages : ~(m.kind = "reply" /\ m.dst = p)}
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]
       /\ pc' = [pc EXCEPT ![p] = "querying"]
  /\ UNCHANGED <<>>

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "querying"
       /\ iteration[p] >= SlushIterationCount
       /\ messages' = messages \cup {[kind |-> "term", src |-> p, dst |-> "client", payload |-> NoMessage]}
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<color, sample, iteration>>

QueryLoopExit ==
  /\ \E m \in messages :
       /\ m.kind = "term"
       /\ \A p \in SlushLoopProcess : pc[p] = "done"
       /\ messages' = messages \ {m}
       /\ pc' = [pc EXCEPT ![m.src] = "done"]
  /\ UNCHANGED <<color, sample, iteration>>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

AllProcessesDone == \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "done"

Termination == <>(AllProcessesDone)

====