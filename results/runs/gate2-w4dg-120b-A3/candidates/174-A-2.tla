---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

\* Slush has two colors. NoColor marks an uncolored node. NoMessage is a
\* distinguished value that never appears in the message set.
Colors == {NoColor, "red", "blue"}

MessageType == [kind : {"query", "reply", "term"}, from : Node, to : Node, color : Colors]

VARIABLES nodeColor, msgs, pc, sampleSet, iterCount

vars == <<nodeColor, msgs, pc, sampleSet, iterCount>>

TypeOK ==
  /\ nodeColor \in [Node -> Colors]
  /\ msgs \subseteq MessageType
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {0} -> {"ready", "looping", "waiting", "idle", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ iterCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {0} |-> "ready"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ iterCount = [lp \in SlushLoopProcess |-> 0]

AssignColor(n) ==
  /\ nodeColor[n] = NoColor
  /\ \E c \in Colors \ {{NoColor}} : nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sampleSet, iterCount>>

RequireColor(lp) ==
  /\ pc[lp] = "ready"
  /\ nodeColor[HostMapping[lp]] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "looping"]
  /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

QuerySampleSet(lp) ==
  /\ pc[lp] = "looping"
  /\ iterCount[lp] < SlushIterationCount
  /\ \E s \in SUBSET (Node \ {HostMapping[lp]}) :
       /\ Cardinality(s) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = s]
  /\ msgs' = msgs \cup {[kind |-> "query", from |-> HostMapping[lp], to |-> q, color |-> nodeColor[HostMapping[lp]]] : q \in sampleSet[lp]}
  /\ UNCHANGED <<nodeColor, pc, iterCount>>

RespondToQuery(m) ==
  /\ m.kind = "query"
  /\ m \in msgs
  /\ \E q \in SlushQueryProcess :
       /\ HostMapping[q] = m.to
       /\ ~ \E other \in msgs : other.kind = "query" /\ other.from = m.from /\ other.to = m.to
       /\ LET c == IF nodeColor[m.to] = NoColor THEN m.color ELSE nodeColor[m.to] IN
            /\ nodeColor' = [nodeColor EXCEPT ![m.to] = c]
            /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", from |-> m.to, to |-> m.from, color |-> c]}
  /\ UNCHANGED <<pc, sampleSet, iterCount>>

FinishReply(m) ==
  /\ m.kind = "reply"
  /\ m \in msgs
  /\ \E lp \in SlushLoopProcess :
       /\ HostMapping[lp] = m.from
       /\ m.to = HostMapping[lp]
       /\ m.from \in sampleSet[lp]
  /\ iterCount' = [lp \in SlushLoopProcess |-> IF HostMapping[lp] = m.from THEN iterCount[lp] + 1 ELSE iterCount[lp]]
  /\ pc' = [lp \in SlushLoopProcess |-> IF HostMapping[lp] = m.from /\ iterCount[lp] + 1 = SlushIterationCount THEN "idle" ELSE pc[lp]]
  /\ sampleSet' = [lp \in SlushLoopProcess |-> IF HostMapping[lp] = m.from THEN {} ELSE sampleSet[lp]]
  /\ msgs' = msgs \ {m}

LoopTerminate(lp) ==
  /\ pc[lp] = "idle"
  /\ pc' = [pc EXCEPT ![lp] = "done"]
  /\ msgs' = msgs \cup {[kind |-> "term", from |-> HostMapping[lp], to |-> NoMessage, color |-> NoColor}]
  /\ UNCHANGED <<nodeColor, sampleSet, iterCount>>

QueryLoopExit(q) ==
  /\ pc[q] = "ready"
  /\ \A m \in msgs : m.kind = "term"
  /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

ClientStep ==
  \/ \E n \in Node : AssignColor(n)
  \/ \E lp \in SlushLoopProcess : RequireColor(lp)
  \/ \E lp \in SlushLoopProcess : QuerySampleSet(lp)
  \/ \E m \in msgs : RespondToQuery(m)
  \/ \E m \in msgs : FinishReply(m)
  \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
  \/ \E q \in SlushQueryProcess : QueryLoopExit(q)

Next == ClientStep

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientStep)

PropertyTermination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {0} : pc[p] = "done")

====