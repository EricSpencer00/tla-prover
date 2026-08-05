---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

(* The Slush protocol is a metastable consensus primitive from the Avalanche    *)
(* whitepaper: nodes repeatedly query random peers and adopt the majority      *)
(* color among respondents.  Because TLA+ has no probabilistic capabilities,   *)
(* this is an executable pseudocode model rather than a statistical one.       *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping
          SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME SlushLoopProcess \cup SlushQueryProcess \cap Node = {}
ASSUME HostMapping \subseteq (SlushLoopProcess \cup SlushQueryProcess) \X Node

VARIABLES nodeColor, messages, pc, sampleSet, iterationCount

vars == <<nodeColor, messages, pc, sampleSet, iterationCount>>

Processes == SlushLoopProcess \cup SlushQueryProcess \cup {"client"}

TypeOK ==
  /\ nodeColor \in [Node -> {NoColor, 1, 2}]
  /\ messages \subseteq (SlushLoopProcess \X SlushQueryProcess) \cup
                     (SlushQueryProcess \X SlushLoopProcess) \cup {NoMessage}
  /\ pc \in [Processes -> 0..6]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterationCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in Processes |-> IF p = "client" THEN 0 ELSE 1]
  /\ sampleSet = [l \in SlushLoopProcess |-> {}]
  /\ iterationCount = [l \in SlushLoopProcess |-> 0]

\* An external client assigns the first color to an uncolored node.
AssignColor ==
  /\ pc["client"] = 0
  /\ \E n \in Node, c \in {1, 2} :
       /\ nodeColor[n] = NoColor
       /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = 1]
  /\ UNCHANGED <<messages, sampleSet, iterationCount>>

\* A loop process waits for its host node to get a color before it starts.
RequireColor ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = 1
       /\ \E n \in Node :
            /\ \E p \in SlushQueryProcess : <<l, n, p>> \in HostMapping
            /\ nodeColor[n] # NoColor
            /\ pc' = [pc EXCEPT ![l] = 2]
       /\ UNCHANGED <<nodeColor, messages, sampleSet, iterationCount>>

\* Sample a random set of peers and send a query to each.
QuerySampleSet ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = 2
       /\ iterationCount[l] < SlushIterationCount
       /\ \E sample \in SUBSET SlushQueryProcess : Cardinality(sample) = SampleSetSize
            /\ \E n \in Node :
                 /\ \E p \in SlushQueryProcess : <<l, n, p>> \in HostMapping
                 /\ messages' = messages \cup {<<l, m>> : m \in sample}
            /\ sampleSet' = [sampleSet EXCEPT ![l] = sample]
       /\ pc' = [pc EXCEPT ![l] = 3]
  /\ UNCHANGED <<nodeColor, iterationCount>>

\* A query process adopts the query's color if it is uncolored, then replies.
RespondToQuery ==
  /\ \E m \in messages :
       /\ m \in SlushLoopProcess \X SlushQueryProcess
       /\ \E n \in Node :
            /\ \E p \in SlushQueryProcess : <<fst(m), n, p>> \in HostMapping
            /\ nodeColor' = [nodeColor EXCEPT ![n] = IF nodeColor[n] = NoColor THEN nodeColor[fst(m)] ELSE nodeColor[n]]
            /\ messages' = (messages \ {m}) \cup {<<snd(m), fst(m)>>}
            /\ UNCHANGED <<pc, sampleSet, iterationCount>>

\* After all replies arrive, count colors and adopt the majority if it flips.
TallyReplies ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = 3
       /\ \A m \in messages : (m \in SlushQueryProcess \X SlushLoopProcess) => fst(m) \notin sampleSet[l]
       /\ LET votes == {snd(m) : m \in messages /\ snd(m) \in SlushLoopProcess /\ fst(m) \in sampleSet[l]}
              tally(c) == Cardinality({x \in votes : nodeColor[x] = c})
          IN \/ \E c \in {1, 2} : tally(c) >= PickFlipThreshold /\ nodeColor' = [nodeColor EXCEPT ![fst(sampleSet[l])] = c]
             \/ nodeColor' = nodeColor
       /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
       /\ iterationCount' = [iterationCount EXCEPT ![l] = iterationCount[l] + 1]
       /\ pc' = [pc EXCEPT ![l] = 4]

Terminate ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = 4
       /\ iterationCount[l] = SlushIterationCount
       /\ messages' = messages \cup {NoMessage}
       /\ pc' = [pc EXCEPT ![l] = 5]
  /\ UNCHANGED <<nodeColor, sampleSet, iterationCount>>

ExitQueryLoop ==
  /\ \E p \in SlushQueryProcess :
       /\ pc[p] = 1
       /\ \A l \in SlushLoopProcess : NoMessage \in messages
       /\ pc' = [pc EXCEPT ![p] = 6]
  /\ UNCHANGED <<nodeColor, messages, sampleSet, iterationCount>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ Terminate \/ ExitQueryLoop

Spec == Init /\ [][Next]_vars /\ WF_vars(AssignColor) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
        /\ WF_vars(Terminate) /\ WF_vars(ExitQueryLoop)

AllProcessesDone == \A p \in Processes : pc[p] = 6

Done == <>AllProcessesDone

====