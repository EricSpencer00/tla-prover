---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES nodeColor, messages, loopState, queryState, sampleSet, loopIters

States == {"idle", "waitingForColor", "querying", "done", "replyLoop", "quit"}

RECURSIVE MapOf(_)
MapOf(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup (MapOf(S \ {x}))

TypeOK ==
  /\ nodeColor \in [Node -> {NoColor, 0, 1}]
  /\ messages \subseteq [type : {"query", "queryReply", "termination"},
                         from : SlushLoopProcess \cup SlushQueryProcess,
                         to : SlushLoopProcess \cup SlushQueryProcess,
                         c : {NoColor, 0, 1}]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ loopState = [p \in SlushLoopProcess |-> "waitingForColor"]
  /\ queryState = [q \in SlushQueryProcess |-> "replyLoop"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopIters = [p \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  \E n \in Node, c \in {0, 1} :
    /\ nodeColor[n] = NoColor
    /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, loopState, queryState, sampleSet, loopIters>>

RequireColor ==
  \E p \in SlushLoopProcess :
    /\ loopState[p] = "waitingForColor"
    /\ LET n == CHOOSE n \in Node : (n, p, q) \in HostMapping
       IN IF nodeColor[n] # NoColor
          THEN loopState' = [loopState EXCEPT ![p] = "idle"]
          ELSE UNCHANGED loopState
    /\ UNCHANGED <<nodeColor, messages, queryState, sampleSet, loopIters>>

LoopQuerySampleSet ==
  \E p \in SlushLoopProcess :
    /\ loopState[p] = "idle"
    /\ loopIters[p] < SlushIterationCount
    /\ sampleSet[p] = {}
    /\ LET n == CHOOSE n \in Node : (n, p, q) \in HostMapping
           otherHosts == {m \in Node : m # n}
           otherProcesses == {q : \E m \in otherHosts : (m, p, q) \in HostMapping}
           sample == CHOOSE s \in SUBSET otherProcesses : Cardinality(s) = SampleSetSize
       IN /\ sampleSet' = [sampleSet EXCEPT ![p] = sample]
          /\ loopState' = [loopState EXCEPT ![p] = "querying"]
          /\ messages' = messages \cup {[type |-> "query", from |-> p, to |-> q, c |-> nodeColor[n] : q \in sample]}
    /\ UNCHANGED <<nodeColor, queryState, loopIters>>

QueryRespond ==
  \E m \in {x \in messages : x.type = "query"} :
    /\ queryState[m.to] = "replyLoop"
    /\ \E n \in Node : (n, m.from, m.to) \in HostMapping
       /\ nodeColor' = [nodeColor EXCEPT ![n] = IF nodeColor[n] = NoColor THEN m.c ELSE nodeColor[n]]
       /\ messages' = (messages \ {m}) \cup {[type |-> "queryReply", from |-> m.to, to |-> m.from, c |-> nodeColor[n]]}
    /\ UNCHANGED <<loopState, queryState, sampleSet, loopIters>>

TallyReplies ==
  \E p \in SlushLoopProcess :
    /\ loopState[p] = "querying"
    /\ sampleSet[p] # {}
    /\ \A q \in sampleSet[p] : [type |-> "queryReply", from |-> q, to |-> p, c |-> nodeColor[CHOOSE n \in Node : (n, p, q) \in HostMapping]] \in messages
    /\ LET tally(c) == Cardinality({q \in sampleSet[p] : [type |-> "queryReply", from |-> q, to |-> p, c |-> c] \in messages})
           n == CHOOSE n \in Node : (n, p, q) \in HostMapping
           newColor == IF tally(0) >= PickFlipThreshold THEN 0
                       ELSE IF tally(1) >= PickFlipThreshold THEN 1
                       ELSE nodeColor[n]
       IN /\ nodeColor' = [nodeColor EXCEPT ![n] = newColor]
          /\ messages' = {x \in messages : ~(x.type = "queryReply" /\ x.to = p)}
          /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
          /\ loopIters' = [loopIters EXCEPT ![p] = loopIters[p] + 1]
          /\ loopState' = [loopState EXCEPT ![p] = "idle"]
    /\ UNCHANGED queryState

LoopTerminate ==
  \E p \in SlushLoopProcess :
    /\ loopState[p] = "idle"
    /\ loopIters[p] >= SlushIterationCount
    /\ loopState' = [loopState EXCEPT ![p] = "done"]
    /\ messages' = messages \cup {[type |-> "termination", from |-> p, to |-> p, c |-> NoColor]}
    /\ UNCHANGED <<nodeColor, queryState, sampleSet, loopIters>>

QueryLoopExit ==
  \E q \in SlushQueryProcess :
    /\ queryState[q] = "replyLoop"
    /\ \A p \in SlushLoopProcess : [type |-> "termination", from |-> p, to |-> p, c |-> NoColor] \in messages
    /\ queryState' = [queryState EXCEPT ![q] = "quit"]
    /\ UNCHANGED <<nodeColor, messages, loopState, sampleSet, loopIters>>

Next ==
  \/ ClientAssignColor \/ RequireColor \/ LoopQuerySampleSet \/ QueryRespond
  \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_<<nodeColor, messages, loopState, queryState, sampleSet, loopIters>>

AllProcessesDone == <>(\A p \in SlushLoopProcess : loopState[p] = "done")

====