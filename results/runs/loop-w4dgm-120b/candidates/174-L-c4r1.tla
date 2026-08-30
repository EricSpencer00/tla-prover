---- MODULE Slush ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

\* The Slush protocol is a metastable consensus scheme where loop processes
\* repeatedly poll sampled peers and adopt a color that reaches a flip
\* threshold. TLC's nondeterminism stands in for the random sampling in a
\* real deployment; there is no timing or fairness to exploit here.
\* The client-request process assigns initial colors to uncolored nodes,
\* which is the only way a node ever enters the protocol.

\* Colors are not named; they are just two distinct values that matter
\* only insofar as two nodes can disagree about which one to pick.
Colors == {"colorA", "colorB"}

RECURSIVE Weigh(_ , _)
Weigh(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Weigh(f, S \ {x})

Variable == [color : {NoColor} \union Colors,
             pc : {"waiting", "querying", "tallying", "done"},
             sampleSet : SUBSET SlushQueryProcess,
             iterations : 0..SlushIterationCount]
Query == [from : SlushLoopProcess, to : SlushQueryProcess, color : Colors]
Reply == [from : SlushQueryProcess, to : SlushLoopProcess, color : Colors]
Term == [from : SlushLoopProcess]

VARIABLES paint, messages, host, loop, query

vars == <<paint, messages, host, loop, query>>

Init ==
  /\ paint = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ host = [p \in SlushLoopProcess |-> CHOOSE m \in HostMapping : m.loop = p]
  /\ loop = [p \in SlushLoopProcess |-> [color |-> NoColor,
                                         pc |-> "waiting",
                                         sampleSet |-> {},
                                         iterations |-> 0]]
  /\ query = [q \in SlushQueryProcess |-> [pc |-> "replying"]]

ServeColor(n, c) ==
  /\ paint[n] = NoColor
  /\ paint' = [paint EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, host, loop, query>>

RequireColor(p) ==
  /\ loop[p].pc = "waiting"
  /\ paint[host[p].node] # NoColor
  /\ loop' = [loop EXCEPT ![p].color = paint[host[p].node],
                          ![p].pc = "querying"]
  /\ UNCHANGED <<paint, messages, host, query>>

QueryPeers(p) ==
  /\ loop[p].pc = "querying"
  /\ loop[p].iterations < SlushIterationCount
  /\ loop[p].sampleSet = {}
  /\ loop[p].color # NoColor
  /\ \E Q \in SUBSET SlushQueryProcess :
       /\ Cardinality(Q) = SampleSetSize
       /\ loop' = [loop EXCEPT ![p].sampleSet = Q]
       /\ messages' = messages \union {[from |-> p, to |-> q, color |-> loop[p].color] : q \in Q}
  /\ UNCHANGED <<paint, host, query>>

Respond(r) ==
  /\ r \in messages
  /\ r \in Query
  /\ query[r.to].pc = "replying"
  /\ IF paint[host[r.to].node] = NoColor
       THEN paint' = [paint EXCEPT ![host[r.to].node] = r.color]
       ELSE paint' = paint
  /\ messages' = (messages \ {r}) \union {[from |-> r.to, to |-> r.from, color |-> paint[host[r.to].node]]}
  /\ UNCHANGED <<host, loop, query>>

\* Tallying only fires once every sampled peer has replied, and only then
\* does the loop process read the votes -- otherwise a late reply would
\* silently be dropped from the count it just performed.
TallyReplies(p) ==
  /\ loop[p].pc = "querying"
  /\ loop[p].sampleSet # {}
  /\ loop[p].sampleSet \subseteq {q \in SlushQueryProcess : [from |-> p, to |-> q, color |-> NoColor] \notin messages}
  /\ \E tallies \in {Weigh([q \in loop[p].sampleSet |-> IF [from |-> q, to |-> p, color |-> NoColor] \in messages THEN 1 ELSE 0],
                         loop[p].sampleSet)} :
       loop' = [loop EXCEPT ![p].pc = IF tallies >= PickFlipThreshold
                                      THEN "tallying"
                                      ELSE "querying",
                          ![p].iterations = loop[p].iterations + 1]
  /\ UNCHANGED <<paint, messages, host, query>>

BroadcastTerm(p) ==
  /\ loop[p].pc = "querying"
  /\ loop[p].iterations = SlushIterationCount
  /\ messages' = messages \union {[from |-> p]}
  /\ loop' = [loop EXCEPT ![p].pc = "done"]
  /\ UNCHANGED <<paint, host, query>>

ExitQueryLoop(q) ==
  /\ query[q].pc = "replying"
  /\ \A p \in SlushLoopProcess : [from |-> p] \in messages
  /\ query' = [query EXCEPT ![q].pc = "done"]
  /\ UNCHANGED <<paint, messages, host, loop>>

CollectTerm(r) ==
  /\ r \in messages
  /\ r \in Term
  /\ messages' = messages \ {r}
  /\ UNCHANGED <<paint, host, loop, query>>

Next ==
  \/ \E n \in Node, c \in Colors : ServeColor(n, c)
  \/ \E p \in SlushLoopProcess : RequireColor(p) \/ QueryPeers(p) \/ TallyReplies(p) \/ BroadcastTerm(p)
  \/ \E q \in SlushQueryProcess : ExitQueryLoop(q)
  \/ \E r \in messages : Respond(r) \/ CollectTerm(r)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Node, c \in Colors : ServeColor(n, c))
  /\ WF_vars(\E p \in SlushLoopProcess : RequireColor(p))
  /\ WF_vars(\E p \in SlushLoopProcess : QueryPeers(p))
  /\ WF_vars(\E r \in messages : Respond(r))
  /\ WF_vars(\E p \in SlushLoopProcess : TallyReplies(p))
  /\ WF_vars(\E p \in SlushLoopProcess : BroadcastTerm(p))
  /\ WF_vars(\E q \in SlushQueryProcess : ExitQueryLoop(q))
  /\ WF_vars(\E r \in messages : CollectTerm(r))

TypeInvariant ==
  /\ paint \in [Node -> {NoColor} \union Colors]
  /\ messages \subseteq (Query \union Reply \union Term)
  /\ host \in [SlushLoopProcess -> HostMapping]
  /\ loop \in [SlushLoopProcess -> Variable]
  /\ query \in [SlushQueryProcess -> [pc : {"replying", "done"}]]

Termination ==
  \A p \in SlushLoopProcess, q \in SlushQueryProcess :
    (loop[p].pc = "done") /\ (query[q].pc = "done")

====