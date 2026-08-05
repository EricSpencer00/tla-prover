---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Slush is the simplest Snow-family protocol: a node samples random peers and
\* adopts a sufficiently popular color. The node set is small and fully connected.
\* Because TLA+ has no probabilistic semantics, the model only approximates the
\* random sampling; convergence is left as an unmodeled (probabilistic) outcome.

\* loopOf / qryOf connect each node to its loop and query processes.
Nodes == Node
Color == {0, 1, NoColor}
Reply == {0, 1}
LoopOf(n) == CHOOSE p \in SlushLoopProcess : <<n, p>> \in HostMapping
QryOf(n) == CHOOSE q \in SlushQueryProcess : <<n, q>> \in HostMapping
QProc == {QryOf(n) : n \in Nodes}
QMsg == [to: QProc, from: SlushLoopProcess, col: Color]
RMsg == [to: SlushLoopProcess, from: QProc, col: Reply]
TMsg == [from: SlushLoopProcess]

VARIABLES assign, msgs, pc, sampleSet, iters

vars == <<assign, msgs, pc, sampleSet, iters>>

TypeOK ==
  /\ assign \in [Nodes -> Color]
  /\ msgs \subseteq (QMsg \cup RMsg \cup TMsg)
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {clientReqProc} -> 0..2]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET QProc]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ assign = [n \in Nodes |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {clientReqProc} |-> 0]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  /\ pc[clientReqProc] = 0
  /\ \E n \in Nodes :
       /\ assign[n] = NoColor
       /\ \E c \in {0, 1} : assign' = [assign EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sampleSet, iters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 0
       /\ assign[CHOOSE n \in Nodes : <<n, p>> \in HostMapping] # NoColor
       /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<assign, msgs, sampleSet, iters>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ \E Q \subseteq QProc :
            /\ Cardinality(Q) = SampleSetSize
            /\ sampleSet' = [sampleSet EXCEPT ![p] = Q]
            /\ msgs' = msgs \cup {[to |-> q, from |-> p, col |-> assign[CHOOSE n \in Nodes : <<n, p>> \in HostMapping]] : q \in Q}
  /\ UNCHANGED <<assign, pc, iters>>

RespondToQuery ==
  /\ \E m \in msgs :
       /\ m \in QMsg
       /\ assign' = IF assign[CHOOSE n \in Nodes : <<n, m.to>> \in HostMapping] = NoColor
                    THEN [assign EXCEPT ![CHOOSE n \in Nodes : <<n, m.to>> \in HostMapping] = m.col]
                    ELSE assign
       /\ msgs' = (msgs \ {m}) \cup {[to |-> m.from, from |-> m.to, col |-> IF assign[CHOOSE n \in Nodes : <<n, m.to>> \in HostMapping] = NoColor
                                                                     THEN m.col ELSE assign[CHOOSE n \in Nodes : <<n, m.to>> \in HostMapping]]}
  /\ UNCHANGED <<pc, sampleSet, iters>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ sampleSet[p] # {}
       /\ \A q \in sampleSet[p] : [to |-> p, from |-> q, col |-> 0] \in msgs \/ [to |-> p, from |-> q, col |-> 1] \in msgs
       /\ LET replies == {m \in msgs : m \in RMsg /\ m.to = p}
              ones == Cardinality({m \in replies : m.col = 1})
              zeros == Cardinality({m \in replies : m.col = 0})
              n == CHOOSE n \in Nodes : <<n, p>> \in HostMapping
              c1 == IF ones >= PickFlipThreshold THEN 1 ELSE assign[n]
              c0 == IF zeros >= PickFlipThreshold THEN 0 ELSE assign[n]
          IN assign' = [assign EXCEPT ![n] = IF ones >= PickFlipThreshold THEN 1 ELSE IF zeros >= PickFlipThreshold THEN 0 ELSE assign[n]]
       /\ msgs' = {m \in msgs : m \notin replies}
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ iters' = [iters EXCEPT ![p] = IF iters[p] < SlushIterationCount THEN iters[p] + 1 ELSE iters[p]]
       /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<pc>>

LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 2
       /\ pc' = [pc EXCEPT ![p] = 3]
       /\ msgs' = msgs \cup {[from |-> p]}
  /\ UNCHANGED <<assign, sampleSet, iters>>

QueryLoopExit ==
  /\ pc[clientReqProc] = 0
  /\ \A p \in SlushLoopProcess : [from |-> p] \in msgs
  /\ \A q \in QProc : pc[q] = 2
  /\ pc' = [pc EXCEPT ![q \in QProc] = 3]
  /\ UNCHANGED <<assign, msgs, sampleSet, iters>>

Next ==
  \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

AllTerminate == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {clientReqProc} : pc[p] = 3)

====