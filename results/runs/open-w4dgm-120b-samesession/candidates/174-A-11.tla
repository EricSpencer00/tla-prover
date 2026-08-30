---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess,
  HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* hostOf(p) is the node that process p belongs to (p is a loop or query process
\* for that node). requiredCount(c) is the number of replies of color c a loop
\* process needs to adopt that color.
hostOf(p) == {n \in Node : <<n, p>> \in HostMapping}
requiredCount(c) == IF c = 1 THEN SampleSetSize ELSE SampleSetSize - 1

VARIABLES color, messages, pc, sampleSet, iterationCount

Message == [kind: {"query", "queryReply", "termination"},
            loop: SlushLoopProcess, query: SlushQueryProcess,
            body: 0..1]

TypeOK ==
  /\ color \in [Node -> (0..1) \union {NoColor}]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \union {NoMessage} -> {"waiting", "querying", "replied", "loopDone", "queryLoopDone"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterationCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess \union {NoMessage} |-> "waiting"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterationCount = [p \in SlushLoopProcess |-> 0]

\* The client assigns a random color to an uncolored node; this repeats until
\* every node has a color.
ClientAssignColor ==
  /\ \E n \in Node, c \in {0, 1} : /\ color[n] = NoColor /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sampleSet, iterationCount>>

RequireColor ==
  /\ \E p \in SlushLoopProcess : /\ pc[p] = "waiting"
                                 /\ \E n \in hostOf(p) : color[n] # NoColor
                                 /\ pc' = [pc EXCEPT ![p] = "querying"]
  /\ UNCHANGED <<color, messages, sampleSet, iterationCount>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "querying"
       /\ iterationCount[p] < SlushIterationCount
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {q \in SlushQueryProcess : q # NoMessage} \cap
                              (CHOOSE S \in SUBSET SlushQueryProcess : Cardinality(S) = SampleSetSize)
       /\ \E q \in sampleSet[p] :
            /\ messages' = messages \union {[kind |-> "query", loop |-> p, query |-> q,
                                             body |-> color[CHOOSE n \in hostOf(p) : TRUE]]}
  /\ pc' = [pc EXCEPT ![p] = "replied"]
  /\ UNCHANGED <<color, iterationCount>>

\* A query process adopts the query's color if it is still uncolored, then
\* replies with whatever color it currently holds.
RespondToQuery ==
  /\ \E m \in messages :
       /\ m.kind = "query" /\ pc[m.query] = "waiting"
       /\ pc' = [pc EXCEPT ![m.query] = "querying"]
       /\ color' = [color EXCEPT ![CHOOSE n \in hostOf(m.query) : TRUE] =
                       IF color[CHOOSE n \in hostOf(m.query) : TRUE] = NoColor THEN m.body
                       ELSE color[CHOOSE n \in hostOf(m.query) : TRUE]]
       /\ messages' = (messages \ {m}) \union
            {[kind |-> "queryReply", loop |-> m.loop, query |-> m.query, body |-> m.body]}
  /\ UNCHANGED <<sampleSet, iterationCount>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "replied" /\ sampleSet[p] # {}
       /\ \A q \in sampleSet[p] : \E m \in messages : m.kind = "queryReply" /\ m.loop = p /\ m.query = q
       /\ LET level(c) == Cardinality({q \in sampleSet[p] : \E m \in messages :
                                         /\ m.kind = "queryReply" /\ m.loop = p /\ m.query = q
                                         /\ m.body = c}) IN
            color' = [n \in Node |-> IF n \in hostOf(p) /\ level(requiredCount(c)) THEN c ELSE color[n]]
       /\ iterationCount' = [iterationCount EXCEPT ![p] = iterationCount[p] + 1]
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ pc' = IF iterationCount[p] + 1 < SlushIterationCount THEN [pc EXCEPT ![p] = "querying"] ELSE [pc EXCEPT ![p] = "loopDone"]
       /\ messages' = {m \in messages : ~(m.kind = "queryReply" /\ m.loop = p)}
  /\ UNCHANGED <<hostOf>>

LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "loopDone" /\ iterationCount[p] = SlushIterationCount
       /\ messages' = messages \union {[kind |-> "termination", loop |-> p, query |-> NoMessage, body |-> 0]}
       /\ pc' = [pc EXCEPT ![p] = "loopDone"]
  /\ UNCHANGED <<color, sampleSet, iterationCount>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "querying"
       /\ \A p \in SlushLoopProcess : pc[p] = "loopDone"
       /\ pc' = [pc EXCEPT ![q] = "queryLoopDone"]
  /\ UNCHANGED <<color, messages, sampleSet, iterationCount>>

Next ==
  \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_<<color, messages, pc, sampleSet, iterationCount>>

TypeInvariant == TypeOK

Termination == <>(\A p \in SlushLoopProcess \union SlushQueryProcess : pc[p] \in {"loopDone", "queryLoopDone"})
====