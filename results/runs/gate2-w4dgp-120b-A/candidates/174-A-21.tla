---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME NoColor \notin Node

\* Slush is a metastable protocol: a node queries a random sample of peers and flips its
\* color to a sufficiently popular one. The model is deterministic in its flow; the
\* randomness of which peers are sampled is captured by nondeterministic choice.
\* Color convergence is a probabilistic property and is deliberately not captured here.

VARIABLES nodeColor, pendingMessages, pc, sampleSet, loopIteration

vars == <<nodeColor, pendingMessages, pc, sampleSet, loopIteration>>

MsgType == [type : {"query", "queryreply", "termination"}, src : SlushQueryProcess \cup SlushLoopProcess, dst : SlushQueryProcess \cup SlushLoopProcess, payload : Node \cup {NoColor}]

Inits ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ pendingMessages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "start"]
  /\ sampleSet = [l \in SlushLoopProcess |-> {}]
  /\ loopIteration = [l \in SlushLoopProcess |-> 0]

Hosts(n) == {hp \in HostMapping : hp[1] = n}
LoopOf(n) == CHOOSE hp \in Hosts(n) : hp[2]
QueryOf(n) == CHOOSE hp \in Hosts(n) : hp[3]

\* The client is the only exponent of the number of colors in the system: it injects
\* color assignments into uncolored nodes. Convergence of every node to one of two
\* colors is the essence of the Snow family.
ClientAssignsColor ==
  /\ pc["client"] = "start"
  /\ \E n \in Node, c \in {n, n} :
       /\ nodeColor[n] = NoColor
       /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "done"]
  /\ UNCHANGED <<pendingMessages, sampleSet, loopIteration>>

RequireColor ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "start"
       /\ nodeColor[LoopOf(l)] # NoColor
       /\ pc' = [pc EXCEPT ![l] = "awaitingcolor"]
  /\ UNCHANGED <<nodeColor, pendingMessages, sampleSet, loopIteration>>

QuerySampleSet ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "awaitingcolor"
       /\ sampleSet[l] = {}
       /\ \E subset \in {ss \in SUBSET SlushQueryProcess : Cardinality(ss) = SampleSetSize} :
            /\ sampleSet' = [sampleSet EXCEPT ![l] = subset]
            /\ pendingMessages' = pendingMessages \cup { [type |-> "query", src |-> l, dst |-> d, payload |-> nodeColor[LoopOf(l)]] : d \in subset }
       /\ pc' = [pc EXCEPT ![l] = "waitingforreplies"]
  /\ UNCHANGED <<nodeColor, loopIteration>>

\* A query process adopts an incoming color for its host if that host is still
\* uncolored; either way it replies with whatever it currently holds.
RespondToQuery ==
  /\ \E q \in pendingMessages :
       /\ q.type = "query"
       /\ pendingMessages' = pendingMessages \ {q}
       /\ nodeColor' = IF nodeColor[LoopOf(q.dst)] = NoColor THEN [nodeColor EXCEPT ![LoopOf(q.dst)] = q.payload] ELSE nodeColor
       /\ pendingMessages' = pendingMessages \cup {[type |-> "queryreply", src |-> q.dst, dst |-> q.src, payload |-> nodeColor[LoopOf(q.dst)]]}
  /\ UNCHANGED <<pc, sampleSet, loopIteration>>

TallyReplies ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "waitingforreplies"
       /\ \A d \in sampleSet[l] : [type |-> "queryreply", src |-> d, dst |-> l, payload |-> nodeColor[LoopOf(d)]] \in pendingMessages
       /\ LET replies == {m \in pendingMessages : m.type = "queryreply" /\ m.dst = l}
              cnt[c \in Node] == Cardinality({m \in replies : m.payload = c})
              cstar \in {c \in Node : cnt[c] >= PickFlipThreshold} \cup {NoColor}
          IN nodeColor' = IF cstar # NoColor THEN [nodeColor EXCEPT ![LoopOf(l)] = cstar] ELSE nodeColor
       /\ pendingMessages' = pendingMessages \ {m \in pendingMessages : m.type = "queryreply" /\ m.dst = l}
       /\ pc' = [pc EXCEPT ![l] = "nextiteration"]
       /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
       /\ loopIteration' = [loopIteration EXCEPT ![l] = @ + 1]
  /\ UNCHANGED <<>>

LoopTermination ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "nextiteration"
       /\ loopIteration[l] < SlushIterationCount
       /\ pc' = [pc EXCEPT ![l] = "awaitingcolor"]
  /\ UNCHANGED <<nodeColor, pendingMessages, sampleSet, loopIteration>>

BroadcastTermination ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "nextiteration"
       /\ loopIteration[l] >= SlushIterationCount
       /\ pendingMessages' = pendingMessages \cup {[type |-> "termination", src |-> l, dst |-> l, payload |-> NoColor]}
       /\ pc' = [pc EXCEPT ![l] = "loopdone"]
  /\ UNCHANGED <<nodeColor, sampleSet, loopIteration>>

QueryProcessExit ==
  /\ \A l \in SlushLoopProcess : pc[l] = "loopdone"
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "awaitingcolor"
       /\ pc' = [pc EXCEPT ![q] = "queryprocessdone"]
  /\ UNCHANGED <<nodeColor, pendingMessages, sampleSet, loopIteration>>

Next == ClientAssignsColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ BroadcastTermination \/ QueryProcessExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignsColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)

TypeInvariant ==
  /\ nodeColor \in [Node -> Node \cup {NoColor}]
  /\ pendingMessages \subseteq MsgType

TerminationProperty == \A p \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[p] \in {"client", "loopdone", "queryprocessdone"})
====