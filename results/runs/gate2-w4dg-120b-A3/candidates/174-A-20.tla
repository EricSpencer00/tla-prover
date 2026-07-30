---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES nodeColor, messages, pc, sampleSet, iterCount

vars == <<nodeColor, messages, pc, sampleSet, iterCount>>

\* A message is a triple; the first component is always the message tag, so
\* NoMessage is a special value that never appears in a real message.
Message == {NoMessage} \cup {"query", "reply", "term"}

RECURSIVE SampleCount(_)
SampleCount(f) ==
  IF f = {} THEN 0
  ELSE LET x == CHOOSE y \in f : TRUE IN f[x] + SampleCount({y \in f : y # x})

TypeInvariant ==
  /\ nodeColor \in [Node -> {NoColor} \cup {"color1", "color2"}]
  /\ messages \subseteq (Message \X (SlushLoopProcess \cup SlushQueryProcess))
  /\ iterCount \in [SlushLoopProcess -> 0..SlushIterationCount]
  /\ \A p \in SlushLoopProcess : p \in Domain(pc)
  /\ \A p \in SlushQueryProcess : p \in Domain(pc)

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "init"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterCount = [p \in SlushLoopProcess |-> 0]

\* The client process assigns initial colors to uncolored nodes.
ClientAssign ==
  /\ \E n \in Node :
       /\ nodeColor[n] = NoColor
       /\ \E col \in {"color1", "color2"} : nodeColor' = [nodeColor EXCEPT ![n] = col]
  /\ UNCHANGED <<messages, pc, sampleSet, iterCount>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "init"
       /\ nodeColor[HostMapping[p].node] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<nodeColor, messages, sampleSet, iterCount>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "sampling"
       /\ iterCount[p] < SlushIterationCount
       /\ \E peers \in SUBSET SlushQueryProcess :
            /\ Cardinality(peers) = SampleSetSize
            /\ peers # {HostMapping[p].query}
            /\ messages' = messages \cup {<<"query">, q, nodeColor[HostMapping[p].node]> : q \in peers}
            /\ sampleSet' = [sampleSet EXCEPT ![p] = peers]
            /\ pc' = [pc EXCEPT ![p] = "tallying"]
  /\ UNCHANGED <<nodeColor, iterCount>>

\* Query processes reply with their current color; the reply is always sent.
RespondQuery ==
  /\ \E qp \in SlushQueryProcess :
       /\ \E m \in messages :
            /\ m[1] = "query" /\ m[2] = qp
            /\ LET sender == m[3] IN
               /\ nodeColor' = IF nodeColor[HostMapping[qp].node] = NoColor
                                 THEN [nodeColor EXCEPT ![HostMapping[qp].node] = sender]
                                 ELSE nodeColor
               /\ messages' = (messages \ {m}) \cup {<<"reply">, qp, nodeColor' [HostMapping[qp].node]>}
  /\ UNCHANGED <<pc, sampleSet, iterCount>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "tallying"
       /\ \A qp \in sampleSet[p] : << "reply", qp >> \in messages
       /\ LET c1 == SampleCount({qp \in sampleSet[p] : nodeColor[HostMapping[qp].node] = "color1"})
            c2 == SampleCount({qp \in sampleSet[p] : nodeColor[HostMapping[qp].node] = "color2"}) IN
            /\ IF c1 >= PickFlipThreshold /\ c2 < PickFlipThreshold
                 THEN nodeColor' = [nodeColor EXCEPT ![HostMapping[p].node] = "color1"]
                 ELSE IF c2 >= PickFlipThreshold /\ c1 < PickFlipThreshold
                    THEN nodeColor' = [nodeColor EXCEPT ![HostMapping[p].node] = "color2"]
                    ELSE nodeColor' = nodeColor
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ iterCount' = [iterCount EXCEPT ![p] = iterCount[p] + 1]
       /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED messages

LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] \in {"sampling", "tallying"}
       /\ iterCount[p] >= SlushIterationCount
       /\ messages' = messages \cup {<<"term">, p>}
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<nodeColor, sampleSet, iterCount>>

QueryLoopExit ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = "replying"
       /\ \A p \in SlushLoopProcess : << "term">, p >> \in messages
       /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<nodeColor, messages, sampleSet, iterCount>>

Next == ClientAssign \/ RequireColor \/ QuerySampleSet \/ RespondQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssign) /\ WF_vars(RespondQuery) /\ WF_vars(QueryLoopExit)

AllDone == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done"

Termination == <>(AllDone)

====