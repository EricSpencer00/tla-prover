---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A SlushLoopProcess drives the main protocol loop for its host node; a
\* SlushQueryProcess replies to incoming queries on behalf of its host.
\* HostMapping links each node to its pair of processes.
\* Slush is a metastable consensus protocol: nodes repeatedly sample peers
\* and adopt the locally popular opinion until convergence.

VARIABLES color, messages, pc, sampleSet, loopIteration

vars == <<color, messages, pc, sampleSet, loopIteration>>

LoopProcesses == SlushLoopProcess
QueryProcesses == SlushQueryProcess
LoopSet == [n \in Node |-> {(n, p, q) \in HostMapping : p \in LoopProcesses}]
QuerySet == [n \in Node |-> {(n, p, q) \in HostMapping : q \in QueryProcesses}]
Typed(n, p, q) == <<n, p, q>> \in HostMapping
MessageIds == {"query", "reply", "term"}

TypeOK ==
  /\ color \in [Node -> {NoColor} \union {"col1", "col2"}]
  /\ messages \subseteq [src: Node, dst: Node, kind: MessageIds, col: {NoColor} \union {"col1", "col2"}]
  /\ pc \in [LoopProcesses -> {"waitingColor", "sampling", "tallying", "done"}]
  /\ loopIteration \in [LoopProcesses -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in LoopProcesses |-> "waitingColor"]
  /\ sampleSet = [p \in LoopProcesses |-> {}]
  /\ loopIteration = [p \in LoopProcesses |-> 0]

MessageTo(p) == CHOOSE q \in QueryProcesses : Typed(color[p], p, q)
MessageFrom(q) == CHOOSE p \in LoopProcesses : Typed(color[p], p, q)

\* The client assigns an initial color to an uncolored node -- the only
\* source of ground truth in the network.
AssignColor ==
  /\ \E n \in Node, c \in {"col1", "col2"} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sampleSet, loopIteration>>

RequireColor ==
  /\ \E p \in LoopProcesses :
       /\ Cardinality(sampleSet[p]) = 0
       /\ \E n \in Node : /\ Typed(color[n], p, MessageTo(p))
                            /\ color[n] # NoColor
                            /\ pc[p] = "waitingColor"
                            /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<color, messages, sampleSet, loopIteration>>

QuerySampleSet ==
  /\ \E p \in LoopProcesses :
       /\ pc[p] = "sampling"
       /\ Cardinality(sampleSet[p]) = 0
       /\ \E s \in [1..SampleSetSize -> Node] :
            /\ Cardinality({s[i] : i \in 1..SampleSize}) = SampleSize
            /\ \A i \in 1..SampleSize :
                 /\ s[i] # color[p]
                 /\ Typed(color[s[i]], p, MessageTo(p))
                 /\ <<s[i], MessageTo(p), "query", color[p]>> \notin messages
                 /\ messages' = messages \union
                      {<<s[i], MessageTo(p), "query", color[p]>>}
            /\ sampleSet' = [sampleSet EXCEPT ![p] = {MessageTo(p)}]
       /\ UNCHANGED <<color, pc, loopIteration>>

RespondToQuery ==
  /\ \E q \in QueryProcesses :
       /\ \E m \in messages :
            /\ m.kind = "query"
            /\ m.dst = q
            /\ \A r \in messages : (r.kind = "query" /\ r.dst = q) => r = m
            /\ LET msg' ==
                 IF color[m.dst] = NoColor
                    THEN [color EXCEPT ![m.dst] = m.col]
                    ELSE color
               IN
                 /\ color' = msg'
                 /\ messages' = (messages \ {m})
                                \union {<<m.dst, m.src, "reply", msg'[m.dst]>>}
  /\ UNCHANGED <<pc, sampleSet, loopIteration>>

\* A loop process only flips its own color once it has heard back from
\* every node it sampled in this round.
TallyReplies ==
  /\ \E p \in LoopProcesses :
       /\ pc[p] = "sampling"
       /\ \A q \in sampleSet[p] : \E m \in messages : m.kind = "reply" /\ m.dst = q /\ m.src = p
       /\ Cardinality(sampleSet[p]) > 0
       /\ LET counts == [c \in {"col1", "col2"} |->
                          Cardinality({q \in sampleSet[p] :
                            \E m \in messages : m.kind = "reply" /\ m.dst = q /\ m.src = p /\ m.col = c})]
          delta == IF \E c \in {"col1", "col2"} : counts[c] >= PickFlipThreshold
                     THEN CHOOSE c \in {"col1", "col2"} : counts[c] >= PickFlipThreshold
                     ELSE NoColor
       IN
         /\ color' = [color EXCEPT ![MessageTo(p)] = IF delta = NoColor THEN color[MessageTo(p)] ELSE delta]
         /\ messages' = {m \in messages : ~(m.kind = "reply" /\ m.dst \in sampleSet[p] /\ m.src = p)}
         /\ pc' = [pc EXCEPT ![p] = IF loopIteration[p] < SlushIterationCount - 1 THEN "sampling" ELSE "done"]
         /\ loopIteration' = [loopIteration EXCEPT ![p] = IF loopIteration[p] < SlushIterationCount THEN @ + 1 ELSE @]
         /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]

LoopTermination ==
  /\ \E p \in LoopProcesses :
       /\ pc[p] = "sampling"
       /\ loopIteration[p] = SlushIterationCount - 1
       /\ pc' = [pc EXCEPT ![p] = "done"]
       /\ messages' = messages \union {<<MessageFrom(p), MessageTo(p), "term", NoColor>>}
  /\ UNCHANGED <<color, sampleSet, loopIteration>>

QueryLoopExit ==
  /\ \A p \in LoopProcesses : pc[p] = "done"
  /\ \A q \in QueryProcesses : \A m \in messages : (m.kind = "term" /\ m.dst = q) => m.src = MessageFrom(q)
  /\ messages' = {}
  /\ UNCHANGED <<color, pc, sampleSet, loopIteration>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(AssignColor) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == <>(\A p \in LoopProcesses : pc[p] = "done")

====