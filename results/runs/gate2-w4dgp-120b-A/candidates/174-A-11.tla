---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(SlushQueryProcess) = Cardinality(SlushLoopProcess)
       /\ \A n \in Node : \E lp \in SlushLoopProcess, qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping

Comment == "Slush uses peer sampling and majority flipping; the invariant below is the only property TLC can check here"

CountIn(S, c) == Cardinality({r \in S : r = c})

VARIABLES color, messages, pc, sampleSet, loopIteration

TypeInvariant ==
  /\ color \in [Node -> (NoColor \cup {"a", "b"})]
  /\ messages \subseteq (SlushLoopProcess \cup SlushQueryProcess \cup NoMessage)

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 0]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ loopIteration = [lp \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  /\ pc["client"] = 0
  /\ \E n \in Node, c \in {"a", "b"} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = 1]
  /\ UNCHANGED <<messages, sampleSet, loopIteration>>

ClientIdle ==
  /\ pc["client"] = 1
  /\ \A n \in Node : color[n] # NoColor
  /\ UNCHANGED <<color, messages, pc, sampleSet, loopIteration>>

RequireColor ==
  /\ \E n \in Node, lp \in SlushLoopProcess :
       /\ <<n, lp>> \in HostMapping
       /\ pc[lp] = 0
       /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = 1]
  /\ UNCHANGED <<color, messages, sampleSet, loopIteration>>

QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 1
       /\ \E ss \in SUBSET (SlushQueryProcess) :
            /\ Cardinality(ss) = SampleSetSize
            /\ sampleSet' = [sampleSet EXCEPT ![lp] = ss]
       /\ pc' = [pc EXCEPT ![lp] = 2]
  /\ UNCHANGED <<color, messages, loopIteration>>

SendQuery ==
  /\ \E lp \in SlushLoopProcess, qp \in SlushQueryProcess :
       /\ pc[lp] = 2
       /\ qp \in sampleSet[lp]
       /\ \E n \in Node : <<n, lp, qp>> \in HostMapping
       /\ messages' = messages \cup {lp}
  /\ UNCHANGED <<color, pc, sampleSet, loopIteration>>

RespondToQuery ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = 0
       /\ \E lp \in messages :
            /\ <<_, lp, qp>> \in HostMapping
            /\ color' = IF color' = [n \in Node |-> color[n]][n \in Node |-> color[n]]
                        THEN [n \in Node |-> IF n = (CHOOSE m \in Node : <<m, lp, qp>> \in HostMapping) THEN color[lp] ELSE color[n]]
                        ELSE [color EXCEPT ![CHOOSE m \in Node : <<m, lp, qp>> \in HostMapping] = color[lp]]
            /\ pc' = [pc EXCEPT ![qp] = 1]
  /\ UNCHANGED <<messages, sampleSet, loopIteration>>

TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 2
       /\ \A qp \in sampleSet[lp] : pc[qp] = 1
       /\ IF \E c \in {"a", "b"} : CountIn({pc[q] : q \in sampleSet[lp]}, c) >= PickFlipThreshold
          THEN color' = [n \in Node |-> IF \E c \in {"a", "b"} : CountIn({pc[q] : q \in sampleSet[lp]}, c) >= PickFlipThreshold THEN c ELSE color[n]]
          ELSE UNCHANGED color
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
       /\ loopIteration' = [loopIteration EXCEPT ![lp] = @ + 1]
       /\ pc' = [pc EXCEPT ![lp] = IF @ + 1 < SlushIterationCount THEN 1 ELSE 3]
  /\ UNCHANGED messages

LoopTerminate ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 3
       /\ messages' = messages \cup {lp}
       /\ pc' = [pc EXCEPT ![lp] = 4]
  /\ UNCHANGED <<color, sampleSet, loopIteration>>

QueryLoopExit ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = 1
       /\ \A lp \in SlushLoopProcess : lp \in messages
       /\ pc' = [pc EXCEPT ![qp] = 3]
  /\ UNCHANGED <<color, messages, sampleSet, loopIteration>>

ResetLoop ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 4
       /\ pc' = [pc EXCEPT ![lp] = 0]
  /\ UNCHANGED <<color, messages, sampleSet, loopIteration>>

Next == ClientAssignColor \/ ClientIdle \/ RequireColor \/ QuerySampleSet \/ SendQuery
        \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit \/ ResetLoop

Spec == Init /\ [][Next]_<<color, messages, pc, sampleSet, loopIteration>>

Termination == <>(\A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : pc[p] = 3)

====