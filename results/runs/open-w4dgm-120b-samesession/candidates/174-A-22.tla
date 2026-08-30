---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

LoopNode == { lp \in SlushLoopProcess : \E n \in Node : <<n, lp>> \in HostMapping }
QueryNode == { qp \in SlushQueryProcess : \E n \in Node : <<n, qp>> \in HostMapping }

RECURSIVE Weight(_)
Weight(S) ==
  IF S = {} THEN 0
  ELSE LET n == CHOOSE x \in S : TRUE IN 1 + Weight(S \ {n})

VARIABLES color, message, pc, sample, loopIter

vars == <<color, message, pc, sample, loopIter>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \union Color]
  /\ message \subseteq (Node \X SlushLoopProcess \X {NoMessage})
                        \union (SlushQueryProcess \X {NoMessage})
                        \union (SlushLoopProcess \X {NoMessage})
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess \union {"clientReq"} -> {"replyLoop", "awaitingColor", "awaitingReplies", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ message = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess \union {"clientReq"} |-> "replyLoop"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ loopIter = [lp \in SlushLoopProcess |-> 0]

AssignColor ==
  /\ pc["clientReq"] = "replyLoop"
  /\ \E n \in Node, c \in Color :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["clientReq"] = "awaitingColor"]
  /\ UNCHANGED <<message, sample, loopIter>>

RequireColor ==
  /\ pc' = [lp \in SlushLoopProcess |->
              IF pc[lp] = "awaitingColor" /\ color[CHOOSE n \in Node : <<n, lp>> \in HostMapping] # NoColor
                THEN "awaitingReplies" ELSE pc[lp]]
  /\ UNCHANGED <<color, message, sample, loopIter>>

QuerySampleSet ==
  /\ pc' = [lp \in SlushLoopProcess |->
              IF pc[lp] = "awaitingReplies" /\ sample[lp] = {}
                THEN LET others == Node \ {CHOOSE n \in Node : <<n, lp>> \in HostMapping}
                         qps == { qp \in SlushQueryProcess : \E n \in others : <<n, qp>> \in HostMapping }
                         pick == CHOOSE Q \in SUBSET qps : Cardinality(Q) = SampleSetSize
                         n == CHOOSE n \in Node : <<n, lp>> \in HostMapping
                     IN [sample EXCEPT ![lp] = pick]
                        /\ message' = message \union { <<qp, lp, color[n]>> : qp \in pick }
                ELSE [sample EXCEPT ![lp] = sample[lp]]]
  /\ UNCHANGED <<color, pc, loopIter>>

RespondQuery ==
  \E qp \in SlushQueryProcess, lp \in SlushLoopProcess, c \in {NoMessage} \union Color :
    /\ <<qp, lp, c>> \in message
    /\ LET n == CHOOSE n \in Node : <<n, qp>> \in HostMapping IN
         color' = IF color[n] = NoColor THEN [color EXCEPT ![n] = c] ELSE color
    /\ message' = (message \ {<<qp, lp, c>>}) \union {<<lp, NoMessage, IF color[n] = NoColor THEN c ELSE color[n]>>}
    /\ pc' = [pc EXCEPT ![lp] = IF pc[lp] = "awaitingReplies" /\ sample[lp] = {} THEN "awaitingColor" ELSE pc[lp]]
    /\ UNCHANGED <<sample, loopIter>>

TallyReplies ==
  \E lp \in SlushLoopProcess :
    /\ pc[lp] = "awaitingReplies"
    /\ \A qp \in sample[lp] : <<lp, NoMessage, NoMessage>> \notin message
    /\ LET tallied == {<<lp, NoMessage, c>> \in message : c # NoMessage }
           counts = [c \in Color |-> Cardinality({ m \in tallied : m[3] = c })]
           winner == CHOOSE c \in Color : counts[c] >= PickFlipThreshold
           n == CHOOSE n \in Node : <<n, lp>> \in HostMapping
       IN /\ color' = [color EXCEPT ![n] = winner]
          /\ message' = { m \in message : m[1] # lp }
          /\ sample' = [sample EXCEPT ![lp] = {}]
          /\ loopIter' = [loopIter EXCEPT ![lp] = IF loopIter[lp] < SlushIterationCount THEN loopIter[lp] + 1 ELSE loopIter[lp]]
    /\ UNCHANGED pc

TerminateLoop ==
  \E lp \in SlushLoopProcess :
    /\ pc[lp] \in {"awaitingColor", "awaitingReplies"}
    /\ loopIter[lp] = SlushIterationCount
    /\ message' = (message \ {<<lp, NoMessage, NoMessage>>}) \union { <<lp, NoMessage, NoMessage>> }
    /\ pc' = [pc EXCEPT ![lp] = "done"]
    /\ UNCHANGED <<color, sample, loopIter>>

QueryLoopExit ==
  /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
  /\ \A qp \in SlushQueryProcess : pc[qp] \in {"replyLoop", "done"}
  /\ pc' = [qp \in SlushQueryProcess |-> IF pc[qp] = "replyLoop" THEN "done" ELSE pc[qp]]
  /\ UNCHANGED <<color, message, sample, loopIter>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet
  \/ RespondQuery \/ TallyReplies \/ TerminateLoop \/ QueryLoopExit

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
  /\ WF_vars(RespondQuery) /\ WF_vars(TallyReplies) /\ WF_vars(TerminateLoop) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \union SlushQueryProcess \union {"clientReq"} : <>(pc[p] = "done")
====