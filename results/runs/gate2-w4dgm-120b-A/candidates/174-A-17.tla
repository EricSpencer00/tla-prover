---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences
CONSTANT Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount
          SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A SlushLoopProcess is the per-node driver of the iteration loop (it queries
\* peers, collects replies, and flips its node's color when a threshold is
\* crossed).  A SlushQueryProcess answers queries about its own node's color.
\* HostMapping links each process to the node it controls.

\* Messages flow in a shared set; there is no ordering, so delivery is nondeterministic.
Message == [kind: {"Query", "QueryReply", "Terminate"}, src: SlushLoopProcess,
            dst: SlushLoopProcess \cup SlushQueryProcess, mcolor: {NoColor} \cup Node]

VARIABLES nodeColor, msgSet, pc, sampleSet, loopIter

TypeOK ==
  /\ nodeColor \in [Node -> {NoColor} \cup Node]
  /\ msgSet \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> 0..1]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

vars == <<nodeColor, msgSet, pc, sampleSet, loopIter>>

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ msgSet = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> 0]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopIter = [p \in SlushLoopProcess |-> 0]

AllLoopDone == \A p \in SlushLoopProcess : pc[p] = 1
AllQueryDone == \A q \in SlushQueryProcess : pc[q] = 1

\* Client assigns an initial color to an uncolored node (one of two colors).
AssignColor ==
  /\ pc["client"] = 0
  /\ \E n \in Node, c \in Node : nodeColor[n] = NoColor /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = 1]
  /\ UNCHANGED <<msgSet, sampleSet, loopIter>>

RequireColor ==
  /\ pc' = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |->
             IF p \in SlushLoopProcess /\ pc[p] = 0 /\ \E n \in Node : n \in HostMapping[p]
             THEN 1 ELSE pc[p]]
  /\ UNCHANGED <<nodeColor, msgSet, sampleSet, loopIter>>

SendQuery ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ loopIter[p] < SlushIterationCount
       /\ sampleSet[p] = {}
       /\ \/ \E Q \in SUBSET SlushQueryProcess :
              /\ Cardinality(Q) = SampleSetSize
              /\ \A q \in Q : \E n \in Node : n \in HostMapping[q]
              /\ sampleSet' = [sampleSet EXCEPT ![p] = Q]
            \* Samples may reappear in a different order; the message set is
            \* a set, not a sequence, so no ordering is assumed here at all.
              /\ msgSet' = {msg \in msgSet : msg.kind # "Query" \/ msg.src # p}
                              \cup {[kind |-> "Query", src |-> p, dst |-> q,
                                    mcolor |-> {n \in Node : n \in HostMapping[p]}]
                                    : q \in Q}
       /\ UNCHANGED <<nodeColor, pc, loopIter>>

Respond ==
  /\ \E m \in msgSet :
       /\ m.kind = "Query"
       /\ m.dst \in SlushQueryProcess
       /\ \E n \in Node : n \in HostMapping[m.dst]
       /\ LET reply == IF nodeColor[n] = NoColor
                       THEN LET c \in m.mcolor : nodeColor' = [nodeColor EXCEPT ![n] = c]
                            m.mcolor
                       ELSE {nodeColor[n]}
          IN msgSet' = (msgSet \ {m}) \cup {[kind |-> "QueryReply", src |-> m.dst,
                                            dst |-> m.src, mcolor |-> reply]}
       /\ UNCHANGED <<pc, sampleSet, loopIter>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ sampleSet[p] # {}
       /\ \A q \in sampleSet[p] : \E m \in msgSet :
            /\ m.kind = "QueryReply"
            /\ m.src = q
            /\ m.dst = p
       /\ \E c \in Node :
            /\ Cardinality({q \in sampleSet[p] : \E m \in msgSet :
                              /\ m.kind = "QueryReply" /\ m.src = q /\ m.dst = p
                              /\ m.mcolor = {c}})
                 >= PickFlipThreshold
            /\ nodeColor' = [nodeColor EXCEPT ![n \in Node : n \in HostMapping[p]] = c]
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ loopIter' = [loopIter EXCEPT ![p] = loopIter[p] + 1]
       /\ UNCHANGED <<msgSet, pc>>

BroadcastTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ loopIter[p] = SlushIterationCount
       /\ msgSet' = msgSet \cup {[kind |-> "Terminate", src |-> p, dst |-> p, mcolor |-> {NoColor}]}
       /\ UNCHANGED <<nodeColor, pc, sampleSet, loopIter>>

QueryLoopExit ==
  /\ AllLoopDone
  /\ \A m \in msgSet : m.kind # "Terminate"
  /\ msgSet' = {}
  /\ pc' = [q \in SlushQueryProcess |-> IF pc[q] = 0 THEN 1 ELSE pc[q]]
  /\ UNCHANGED <<nodeColor, sampleSet, loopIter>>

Next == AssignColor \/ RequireColor \/ SendQuery \/ Respond \/ TallyReplies
        \/ BroadcastTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(Respond) /\ WF_vars(TallyReplies)
        /\ WF_vars(BroadcastTermination) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == AllLoopDone /\ AllQueryDone
====