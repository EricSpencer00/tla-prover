---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount,
  SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A message is always one of three types. The payload varies with the type, but
\* NoMessage stands in for the empty payload of termination messages.
Message == HostMapping \cup [from : SlushLoopProcess, to : SlushQueryProcess,
                              color : {NoColor} \union {"c1", "c2"}]
            \union [from : SlushQueryProcess, to : SlushLoopProcess,
                    color : {NoColor} \union {"c1", "c2"}]
            \union [from : SlushLoopProcess, to : SlushLoopProcess,
                    color : {"terminate"}]

RECURSIVE Count(_, _)
Count(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Count(f, S \ {x})

VARIABLES color, msg, loopPc, queryPc, sample, loopIters

vars == <<color, msg, loopPc, queryPc, sample, loopIters>>

TypeInvariant ==
  /\ color \in [Node -> {NoColor, "c1", "c2"}]
  /\ msg \subseteq Message
  /\ loopPc \in [SlushLoopProcess -> {"waitColor", "sample", "tally", "done"}]
  /\ queryPc \in [SlushQueryProcess -> {"replyLoop", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msg = {}
  /\ loopPc = [p \in SlushLoopProcess |-> "waitColor"]
  /\ queryPc = [q \in SlushQueryProcess |-> "replyLoop"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopIters = [p \in SlushLoopProcess |-> 0]

\* The client process picks an uncolored node and assigns a random color.
ClientAssignColor(n) ==
  /\ color[n] = NoColor
  /\ \E c \in {"c1", "c2"} : color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msg, loopPc, queryPc, sample, loopIters>>

RequireColor(p) ==
  /\ loopPc[p] = "waitColor"
  /\ \E n \in Node : <<p, n>> \in HostMapping /\ color[n] # NoColor
  /\ loopPc' = [loopPc EXCEPT ![p] = "sample"]
  /\ UNCHANGED <<color, msg, queryPc, sample, loopIters>>

\* The loop process builds a random sample of peers and sends them a query.
QuerySampleSet(p) ==
  /\ loopPc[p] = "sample"
  /\ loopIters[p] < SlushIterationCount
  /\ \E Q \in SUBSET SlushQueryProcess :
        /\ Cardinality(Q) = SampleSetSize
        /\ /\forall q \in Q : <<p, q>> \notin msg
           /\ msg' = msg \union {[from |-> p, to |-> q, color |-> "unquery"]
                                 : q \in Q}
  /\ sample' = [sample EXCEPT ![p] = Q]
  /\ loopPc' = [loopPc EXCEPT ![p] = "tally"]
  /\ UNCHANGED <<color, queryPc, loopIters>>

\* A query process adopts the query color if it is still uncolored, then replies.
RespondToQuery(q, p) ==
  /\ loopPc[p] = "tally"
  /\ <<p, q>> \in msg
  /\ color' = IF \E n \in Node : <<q, n>> \in HostMapping /\ color[n] # NoColor
              THEN LET n == CHOOSE m \in Node : <<q, m>> \in HostMapping IN [color EXCEPT ![n] = "c1"]
              ELSE color
  /\ msg' = (msg \ {<<p, q>>}) \union {[from |-> q, to |-> p, color |-> "unquery"]}
  /\ UNCHANGED <<loopPc, queryPc, sample, loopIters>>

\* Once all replies are in, the loop adopts a majority color if one exists.
TallyReplies(p) ==
  /\ loopPc[p] = "tally"
  /\ \A q \in sample[p] : <<q, p>> \in msg
  /\ Cardinality({q \in sample[p] : [from |-> q, to |-> p, color |-> "unquery"] \in msg
                                          /\ color[[q \in Node : <<q, n>> \in HostMapping /\ n = n] = n] = "c1"}) >= PickFlipThreshold
       \/ Cardinality({q \in sample[p] : [from |-> q, to |-> p, color |-> "unquery"] \in msg
                                          /\ color[[q \in Node : <<q, n>> \in HostMapping /\ n = n] = n] = "c2"}) >= PickFlipThreshold
  /\ color' = IF Cardinality({q \in sample[p] : [from |-> q, to |-> p, color |-> "unquery"] \in msg
                                          /\ color[[q \in Node : <<q, n>> \in HostMapping /\ n = n] = n] = "c1"}) >= PickFlipThreshold
              THEN [color EXCEPT ![CHOOSE n \in Node : <<p, n>> \in HostMapping] = "c1"]
              ELSE [color EXCEPT ![CHOOSE n \in Node : <<p, n>> \in HostMapping] = "c2"]
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ loopIters' = [loopIters EXCEPT ![p] = @ + 1]
  /\ loopPc' = IF loopIters[p] + 1 < SlushIterationCount THEN "sample" ELSE "done"
  /\ msg' = msg \ {<<p, q>> : q \in sample[p]}
  /\ UNCHANGED queryPc

LoopTermination(p) ==
  /\ loopPc[p] = "done"
  /\ \A q \in SlushQueryProcess : [from |-> p, to |-> q, color |-> "terminate"] \notin msg
  /\ msg' = msg \union {[from |-> p, to |-> q, color |-> "terminate"] : q \in SlushQueryProcess}
  /\ UNCHANGED <<color, loopPc, queryPc, sample, loopIters>>

QueryLoopExit(q) ==
  /\ queryPc[q] = "replyLoop"
  /\ \A p \in SlushLoopProcess : [from |-> p, to |-> q, color |-> "terminate"] \in msg
  /\ queryPc' = [queryPc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, msg, loopPc, sample, loopIters>>

Next ==
  \/ \E n \in Node : ClientAssignColor(n)
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : QuerySampleSet(p)
  \/ \E q \in SlushQueryProcess, p \in SlushLoopProcess : RespondToQuery(q, p)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : LoopTermination(p)
  \/ \E q \in SlushQueryProcess : QueryLoopExit(q)

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopTermination("p1")) /\ WF_vars(LoopTermination("p2"))
        /\ WF_vars(LoopTermination("p3")) /\ WF_vars(TallyReplies("p1"))
        /\ WF_vars(TallyReplies("p2")) /\ WF_vars(TallyReplies("p3"))

AllProcessesDone ==
  /\ \A p \in SlushLoopProcess : loopPc[p] = "done"
  /\ \A q \in SlushQueryProcess : queryPc[q] = "done"

Termination == <>(AllProcessesDone)

====