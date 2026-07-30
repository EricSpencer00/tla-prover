---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess,
  HostMapping, SlushIterationCount, SampleSetSize,
  PickFlipThreshold, NoColor, NoMessage

\* Colors are identified by the loop processes that currently back them.
Color == SlushLoopProcess \cup {NoColor}

Message == [tgt: SlushQueryProcess \cup SlushLoopProcess,
            src: SlushLoopProcess,
            kind: {"query", "reply", "term"},
            col: Color]

VARIABLES colorOf, messages, pc, sampleSet, itersDone

vars == << colorOf, messages, pc, sampleSet, itersDone >>

QueryProc(n) ==
  CHOOSE q \in SlushQueryProcess : [node |-> n, kind |-> "query"] \in HostMapping
LoopProc(n) ==
  CHOOSE l \in SlushLoopProcess : [node |-> n, kind |-> "loop"] \in HostMapping

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {clientReq} |-> "start"]
  /\ sampleSet = [l \in SlushLoopProcess |-> {}]
  /\ itersDone = [l \in SlushLoopProcess |-> 0]

AssignColor ==
  /\ pc[clientReq] = "start"
  /\ \E n \in Node :
       /\ colorOf[n] = NoColor
       /\ \E c \in Color \ {NoColor} : colorOf' = [colorOf EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT ![clientReq] = "start"]
  /\ UNCHANGED << messages, sampleSet, itersDone >>

\* Loop processes wait until their node is colored before starting.
RequireColor ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "start"
       /\ colorOf[LoopProc(l).node] # NoColor
       /\ pc' = [pc EXCEPT ![l] = "awaitSample"]
  /\ UNCHANGED << colorOf, messages, sampleSet, itersDone >>

QuerySampleSet ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "awaitSample"
       /\ Cardinality(sampleSet[l]) < SampleSetSize
       /\ \E q \in SlushQueryProcess \ { q \in sampleSet[l] } :
            /\ colorOf[LoopProc(l).node] # NoColor
            /\ sampleSet' = [sampleSet EXCEPT ![l] = @ \cup {q}]
            /\ messages' = messages \cup {[tgt |-> q, src |-> l,
                                          kind |-> "query",
                                          col |-> colorOf[LoopProc(l).node]]}
  /\ UNCHANGED << colorOf, pc, itersDone >>

RespondToQuery ==
  /\ \E m \in messages :
       /\ m.kind = "query"
       /\ LET q == m.tgt
              n == (CHOOSE nd \in Node : [node |-> nd, kind |-> "query"] \in HostMapping
                                            /\ nd = q.node)
       /\ colorOf' = [colorOf EXCEPT ![n] =
                        IF colorOf[n] = NoColor THEN m.col ELSE colorOf[n]]
       /\ messages' = (messages \ {m}) \cup {[tgt |-> m.src, src |-> q,
                                            kind |-> "reply",
                                            col |-> colorOf[n]]}
  /\ UNCHANGED << pc, sampleSet, itersDone >>

TallyReplies ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "awaitSample"
       /\ sampleSet[l] # {}
       /\ \A q \in sampleSet[l] : \E m \in messages :
            /\ m.kind = "reply"
            /\ m.src = q
            /\ m.tgt = l
       /\ LET colCount(c) ==
              Cardinality({q \in sampleSet[l] : \E m \in messages :
                             /\ m.kind = "reply"
                             /\ m.tgt = l
                             /\ m.src = q
                             /\ m.col = c})
          newColor == IF colCount(NoColor) >= PickFlipThreshold THEN NoColor
                      ELSE IF colCount(NoColor \cup {l}) >= PickFlipThreshold
                           THEN l ELSE colorOf[LoopProc(l).node]
       /\ colorOf' = [colorOf EXCEPT ![LoopProc(l).node] = newColor]
       /\ messages' = {m \in messages :
                         ~ (m.kind = "reply" /\ m.tgt = l /\ m.src \in sampleSet[l])}
       /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
       /\ itersDone' = [itersDone EXCEPT ![l] = IF itersDone[l] < SlushIterationCount
                                                   THEN @ + 1 ELSE @]
       /\ pc' = [pc EXCEPT ![l] =
                    IF itersDone[l] >= SlushIterationCount THEN "done" ELSE "awaitSample"]
  /\ UNCHANGED << >>

BroadcastTerm ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "done"
       /\ pc' = [pc EXCEPT ![l] = "done"]
  /\ UNCHANGED << colorOf, messages, sampleSet, itersDone >>

ExitQueryLoop ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "awaitReply"
       /\ \A l \in SlushLoopProcess : pc[l] = "done"
       /\ \A m \in messages : m.kind # "term"
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED << colorOf, messages, sampleSet, itersDone >>

Next ==
  \/ AssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ BroadcastTerm
  \/ ExitQueryLoop

Spec == Init /\ [][Next]_vars
        /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)

TypeInvariant ==
  /\ colorOf \in [Node -> Color]
  /\ messages \subseteq Message

====