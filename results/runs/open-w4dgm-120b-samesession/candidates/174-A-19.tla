---- MODULE Slush ----
(* Slush is the simplest member of the Avalanche family's probabilistic
   consensus protocols. Nodes repeatedly sample a random subset of peers
   and adopt a popular opinion, racing to a single converged color. TLA+
   has no probabilistic reasoning, so this serves as executable
   pseudocode for the protocol: the actions model client color
   assignment, looping queries, and reply processing, but convergence is
   not verified here. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
           SlushIterationCount, SampleSetSize, PickFlipThreshold,
           NoColor, NoMessage

VARIABLES nodeColor, messageSet, pc, sampleSet, loopIters

TypeOK ==
    /\ nodeColor \in [Node -> {NoColor} \union {"color1", "color2"}]
    /\ messageSet \subseteq [kind: {NoMessage, "reply", "quit"},
                            by: SlushQueryProcess \union {NoMessage},
                            to: SlushLoopProcess \union {NoMessage},
                            payload: {NoColor} \union {"color1", "color2"}]
    /\ pc \in [SlushLoopProcess -> {"waitColor", "samplePeers", "waitResponses", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopIters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ messageSet = {}
    /\ pc = [lp \in SlushLoopProcess |-> "waitColor"]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ loopIters = [lp \in SlushLoopProcess |-> 0]

Host(n) == CHOOSE p \in HostMapping : p[1] = n

AssignColor ==
    /\ \E n \in Node, c \in {"color1", "color2"} :
         /\ nodeColor[n] = NoColor
         /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
    /\ UNCHANGED <<messageSet, pc, sampleSet, loopIters>>

RequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "waitColor"
         /\ nodeColor[Host(lp)[1]] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = "samplePeers"]
    /\ UNCHANGED <<nodeColor, messageSet, sampleSet, loopIters>>

QueryPeers ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "samplePeers"
         /\ loopIters[lp] < SlushIterationCount
         /\ \E ss \in SUBSET SlushQueryProcess :
              /\ Cardinality(ss) = SampleSetSize
              /\ sampleSet' = [sampleSet EXCEPT ![lp] = ss]
         /\ messageSet' = messageSet \union
              {[kind |-> NoMessage, by |-> NoMessage, to |-> lp, payload |-> nodeColor[Host(lp)[1]]]
                 : qp \in sampleSet[lp]}
    /\ UNCHANGED <<nodeColor, pc, loopIters>>

RespondToQuery ==
    /\ \E m \in messageSet :
         /\ m.kind = NoMessage
         /\ \/ LET p == Host(m.by)[1] IN
              /\ nodeColor[p] = NoColor
              /\ nodeColor' = [nodeColor EXCEPT ![p] = m.payload]
              /\ UNCHANGED <<pc, sampleSet, loopIters>>
            \/ nodeColor' = nodeColor
         /\ messageSet' = (messageSet \ {m}) \union
              {[kind |-> "reply", by |-> m.by, to |-> m.to, payload |-> nodeColor[Host(m.by)[1]]]}
    /\ UNCHANGED <<pc, sampleSet, loopIters>>

TallyReplies ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "waitResponses"
         /\ \A qp \in sampleSet[lp] : \E m \in messageSet : m.kind = "reply" /\ m.by = qp /\ m.to = lp
         /\ LET votes == [c \in {"color1", "color2"} |->
                             Cardinality({qp \in sampleSet[lp] : \E m \in messageSet :
                                              m.kind = "reply" /\ m.by = qp /\ m.payload = c})]
            IN nodeColor' = [nodeColor EXCEPT ![Host(lp)[1]] =
                                IF votes["color1"] >= PickFlipThreshold THEN "color1"
                                ELSE IF votes["color2"] >= PickFlipThreshold THEN "color2"
                                ELSE nodeColor[Host(lp)[1]]]
         /\ messageSet' = {m \in messageSet : ~(m.kind = "reply" /\ m.to = lp)}
         /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
         /\ loopIters' = [loopIters EXCEPT ![lp] = @ + 1]
         /\ pc' = [pc EXCEPT ![lp] = IF loopIters[lp] + 1 < SlushIterationCount
                                      THEN "samplePeers" ELSE "done"]
    /\ UNCHANGED <<>>

LoopTermination ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "waitResponses"
         /\ Cardinality(sampleSet[lp]) = 0
         /\ \A qp \in sampleSet[lp] : \E m \in messageSet : m.kind = "reply" /\ m.by = qp /\ m.to = lp
         /\ pc' = [pc EXCEPT ![lp] = "done"]
    /\ UNCHANGED <<nodeColor, messageSet, sampleSet, loopIters>>

BroadcastQuit ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "done"
         /\ loopIters[lp] = SlushIterationCount
         /\ messageSet' = messageSet \union
              {[kind |-> "quit", by |-> NoMessage, to |-> lp, payload |-> NoColor]}
    /\ UNCHANGED <<nodeColor, pc, sampleSet, loopIters>>

QueryLoopExit ==
    /\ \E qp \in SlushQueryProcess :
         /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
         /\ messageSet' = messageSet \union
              {[kind |-> NoMessage, by |-> qp, to |-> NoMessage, payload |-> NoColor]}
    /\ UNCHANGED <<nodeColor, pc, sampleSet, loopIters>>

Next == AssignColor \/ RequireColor \/ QueryPeers \/ RespondToQuery \/ TallyReplies
        \/ LoopTermination \/ BroadcastQuit \/ QueryLoopExit

Spec == Init /\ [][Next]_<<nodeColor, messageSet, pc, sampleSet, loopIters>>

ProcessTermination == \A lp \in SlushLoopProcess : (pc[lp] = "samplePeers") ~> (pc[lp] = "done")
====