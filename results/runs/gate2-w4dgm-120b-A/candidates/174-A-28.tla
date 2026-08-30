---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* hostNode[p] = the node that process p runs on (used for both loop and query processes)
hostNode == {n \in Node : <<n, SlushLoopProcess, NoMessage>> \in HostMapping} \cup
            {n \in Node : <<n, SlushQueryProcess, NoMessage>> \in HostMapping}

VARIABLES color, inbox, pc, sampleSet, loopsCompleted

vars == <<color, inbox, pc, sampleSet, loopsCompleted>>

\* Four kinds of messages circulate: a query, a query reply, a termination broadcast, and NoMessage (no message)
TypeOK ==
  /\ color \in [Node -> {NoColor, 0, 1}]
  /\ inbox \subseteq {NoMessage} \cup
       [dest: SlushQueryProcess \cup SlushLoopProcess, from: Node, kind: {"query", "reply", "term"}, color: {NoColor, 0, 1}]
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"ready", "waiting", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ loopsCompleted \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "ready"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopsCompleted = [p \in SlushLoopProcess |-> 0]

\* The client assigns a random color to an uncolored node straight out of the pool
AssignColor ==
  \E n \in Node, c \in {0, 1}:
    /\ color[n] = NoColor
    /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<inbox, pc, sampleSet, loopsCompleted>>

RequireColor(p) ==
  /\ pc[p] = "ready"
  /\ color[hostNode[p]] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<color, inbox, sampleSet, loopsCompleted>>

\* Loop processes query a random subset of peers; the sample set records who was asked
QuerySample(p) ==
  \E s \in SUBSET (Node \ {hostNode[p]}):
    /\ pc[p] = "waiting"
    /\ loopsCompleted[p] < SlushIterationCount
    /\ Cardinality(s) = SampleSetSize
    /\ inbox' = inbox \cup {[dest |-> SlushQueryProcess, from |-> hostNode[p], kind |-> "query", color |-> color[hostNode[p]]]}
    /\ sampleSet' = [sampleSet EXCEPT ![p] = s]
    /\ UNCHANGED <<color, pc, loopsCompleted>>

\* A query process adopts the query's color if it is still uncolored, then replies
RespondQuery ==
  \E m \in inbox:
    /\ m.kind = "query"
    /\ LET n == hostNode[m.from] IN
        /\ LET q == hostNode[m.dest] IN
            /\ color' = [color EXCEPT ![q] =
                 IF color[q] = NoColor THEN m.color ELSE color[q]]
            /\ inbox' = (inbox \ {m})
                 \cup {[dest |-> SlushLoopProcess, from |-> n, kind |-> "reply", color |-> color[q]]}
    /\ UNCHANGED <<pc, sampleSet, loopsCompleted>>

\* The loop process flips its own node's color once a color meets the flip threshold
TallyReplies(p) ==
  \E replies \in SUBSET [from: Node, color: {NoColor, 0, 1}]:
    /\ pc[p] = "waiting"
    /\ loopsCompleted[p] < SlushIterationCount
    /\ inbox' = inbox \ {m \in inbox : m.dest = SlushLoopProcess /\ m.from \in sampleSet[p]}
    /\ LET colorCounts ==
         [c \in {0, 1} |->
            Cardinality({m \in replies : m.color = c /\ m.from \in sampleSet[p]})]
       IN LET newColor ==
            IF \E c \in {0, 1} : colorCounts[c] >= PickFlipThreshold
              THEN CHOOSE c \in {0, 1} : colorCounts[c] >= PickFlipThreshold
              ELSE color[hostNode[p]]
       IN color' = [color EXCEPT ![hostNode[p]] = newColor]
    /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
    /\ loopsCompleted' = [loopsCompleted EXCEPT ![p] = loopsCompleted[p] + 1]
    /\ UNCHANGED pc

LoopTerminate(p) ==
  /\ pc[p] = "waiting"
  /\ loopsCompleted[p] = SlushIterationCount
  /\ inbox' = inbox \cup {[dest |-> SlushLoopProcess, from |-> hostNode[p], kind |-> "term", color |-> NoColor]}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<color, sampleSet, loopsCompleted>>

\* Query processes exit once every loop process has terminated
QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \A q \in SlushQueryProcess : pc[q] = "ready"
  /\ pc' = [pc EXCEPT ![q] = "done" \in SlushQueryProcess]
  /\ UNCHANGED <<color, inbox, sampleSet, loopsCompleted>>

Next ==
  \/ AssignColor
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : QuerySample(p)
  \/ RespondQuery
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : LoopTerminate(p)
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

\* No query or reply message is ever left in the set once every loop process has finished
Termination ==
  (\A p \in SlushLoopProcess : pc[p] = "done") ~>
    (\A q \in SlushLoopProcess \cup SlushQueryProcess : pc[q] = "done")

====