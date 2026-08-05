---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Slush is a metastable consensus protocol: every node starts uncolored, then
\* repeatedly samples random peers and adopts a color that a strict majority of
\* its sample reported. Once a node is colored it never flips again.
\* While the real protocol relies on random sampling to converge, TLA+ has no
\* probabilistic model, so this spec only implements the deterministic
\* control flow; a convergence invariant is deliberately omitted.

VARIABLES slushColor, slushMessage, slushCounter, slushSample, slushIterations

vars == <<slushColor, slushMessage, slushCounter, slushSample, slushIterations>>

SlushLoopProcessSet == { p[1] : p \in HostMapping }
SlushQueryProcessSet == { p[2] : p \in HostMapping }

SlushLoopQueryMsg == [ sample : Node, sender : SlushLoopProcess, payload : 1..2 ]
SlushQueryReplyMsg == [ sample : Node, sender : SlushQueryProcess, payload : 1..2 ]
SlushTerminateMsg == [ sample : Node, sender : SlushLoopProcess ]

SlushReplyCount(clr) ==
  Cardinality({ m \in slushMessage : m \in SlushQueryReplyMsg /\ m.payload = clr })

TypeInvariant ==
  /\ slushColor \in [ Node -> { 1, 2, NoColor } ]
  /\ slushMessage \subseteq (SlushLoopQueryMsg \cup SlushQueryReplyMsg \cup { SlushTerminateMsg })
  /\ slushCounter \in [ (SlushLoopProcess \cup SlushQueryProcess) -> 0..3 ]
  /\ slushSample \in [ SlushLoopProcess -> SUBSET Node ]
  /\ slushIterations \in [ SlushLoopProcess -> 0..SlushIterationCount ]

Init ==
  /\ slushColor = [ n \in Node |-> NoColor ]
  /\ slushMessage = {}
  /\ slushCounter = [ p \in (SlushLoopProcess \cup SlushQueryProcess) |-> 0 ]
  /\ slushSample = [ p \in SlushLoopProcess |-> {} ]
  /\ slushIterations = [ p \in SlushLoopProcess |-> 0 ]

\* The client assigns an initial color to a still-uncolored node.
ClientAssignColor ==
  /\ slushCounter[SlushQueryProcessSet] = 0
  /\ \E n \in Node :
       /\ slushColor[n] = NoColor
       /\ \E clr \in { 1, 2 } : slushColor' = [ slushColor EXCEPT ![n] = clr ]
  /\ UNCHANGED << slushMessage, slushCounter, slushSample, slushIterations >>

RequireColor ==
  /\ slushCounter[SlushLoopProcessSet] = 0
  /\ \E p \in SlushLoopProcess :
       /\ slushCounter[p] = 0
       /\ slushColor[CHOOSE n \in Node : \E qp \in SlushQueryProcessSet : <n, qp> \in HostMapping /\ qp = p ] # NoColor
       /\ slushCounter' = [ slushCounter EXCEPT ![p] = 1 ]
  /\ UNCHANGED << slushColor, slushMessage, slushSample, slushIterations >>

\* A loop process samples a fixed-size subset of other nodes and queries them,
\* sending its current color as the payload.
QuerySampleSet ==
  /\ slushCounter[SlushLoopProcessSet] = 1
  /\ \E p \in SlushLoopProcess :
       /\ slushCounter[p] = 1
       /\ slushIterations[p] < SlushIterationCount
       /\ \E peers \in SUBSET Node :
            /\ Cardinality(peers) = SampleSetSize
            /\ \A m \in peers : m # CHOOSE n \in Node : <n, p> \in HostMapping
            /\ slushSample' = [ slushSample EXCEPT ![p] = peers ]
            /\ slushMessage' = slushMessage \cup { [ sample = n, sender = p, payload = slushColor[CHOOSE n \in Node : <n, p> \in HostMapping] ] : n \in peers }
       /\ slushCounter' = [ slushCounter EXCEPT ![p] = 2 ]
  /\ UNCHANGED << slushColor, slushIterations >>

\* A query process adopts an incoming query's color if uncolored, then replies.
RespondToQuery ==
  /\ slushCounter[SlushQueryProcessSet] = 0
  /\ \E m \in slushMessage :
       /\ m \in SlushLoopQueryMsg
       /\ slushMessage' = (slushMessage \ { m }) \cup { [ sample = m.sample, sender = p, payload = IF slushColor[m.sample] = NoColor THEN m.payload ELSE slushColor[m.sample] ] : p \in SlushQueryProcessSet }
  /\ UNCHANGED << slushColor, slushCounter, slushSample, slushIterations >>

\* The loop process waits for every sampled peer's reply, then flips to a color
\* that has reached the majority threshold in this round's sample.
TallyReplies ==
  /\ slushCounter[SlushLoopProcessSet] = 2
  /\ \E p \in SlushLoopProcess :
       /\ slushCounter[p] = 2
       /\ \A n \in slushSample[p] : slushMessage \cap SlushQueryReplyMsg = { m \in slushMessage : m \in SlushQueryReplyMsg /\ m.sample = n }
       /\ IF SlushReplyCount(1) >= PickFlipThreshold THEN slushColor' = [ slushColor EXCEPT ![CHOOSE n \in Node : <n, p> \in HostMapping] = 1 ]
          ELSE IF SlushReplyCount(2) >= PickFlipThreshold THEN slushColor' = [ slushColor EXCEPT ![CHOOSE n \in Node : <n, p> \in HostMapping] = 2 ]
          ELSE slushColor' = slushColor
       /\ slushSample' = [ slushSample EXCEPT ![p] = {} ]
       /\ slushIterations' = [ slushIterations EXCEPT ![p] = IF slushIterations[p] < SlushIterationCount THEN slushIterations[p] + 1 ELSE slushIterations[p] ]
       /\ slushCounter' = [ slushCounter EXCEPT ![p] = 3 ]
  /\ UNCHANGED << slushMessage >>

LoopTermination ==
  /\ slushCounter[SlushLoopProcessSet] = 3
  /\ \E p \in SlushLoopProcess :
       /\ slushCounter[p] = 3
       /\ slushMessage' = slushMessage \cup { [ sample = CHOOSE n \in Node : <n, p> \in HostMapping, sender = p ] }
       /\ slushCounter' = [ slushCounter EXCEPT ![p] = 4 ]
  /\ UNCHANGED << slushColor, slushSample, slushIterations >>

QueryLoopExit ==
  /\ slushCounter[SlushLoopProcessSet] = 4
  /\ slushMessage \cap SlushTerminateMsg = {}
  /\ slushCounter[SlushQueryProcessSet] < 4
  /\ slushCounter' = [ p \in SlushQueryProcessSet |-> 4 ]
  /\ slushMessage' = slushMessage \cup SlushTerminateMsg
  /\ UNCHANGED << slushColor, slushSample, slushIterations >>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)

Termination ==
  /\ \A p \in (SlushLoopProcess \cup SlushQueryProcess) : slushCounter[p] = 4
  /\ UNCHANGED vars

====