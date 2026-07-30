---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

\* Each node has a loop process that runs the Slush iteration, and a query
\* process that answers the loop's sampled polls.
\* The model is checked against a tiny config (3 nodes, 1 iteration) and a
\* medium config (more nodes / iterations) using the same spec.

\* Types: color assignment, the in-flight message set, each process pc, the
\* current sample set per loop, and each loop's iteration counter.
VARIABLES
  slushColor,
  messages,
  pc,
  sampleSet,
  loopsDone

Message == [kind: {"query", "reply", "term"}, src: Node, dst: Node, col: {NoColor} \union {0, 1}]
LoopStates == {"waiting", "sampling", "tallying", "done"}
QueryStates == {"replies", "done"}

TypeInvariant ==
  /\ slushColor \in [Node -> {NoColor} \union {0, 1}]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess -> LoopStates \union QueryStates]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ loopsDone \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ slushColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess |-> IF p \in SlushLoopProcess THEN "waiting" ELSE "replies"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopsDone = [p \in SlushLoopProcess |-> 0]

\* Client assigns a random color to an uncolored node (the transactions).
AssignColor ==
  \E n \in Node, col \in {0, 1} :
    /\ slushColor[n] = NoColor
    /\ slushColor' = [slushColor EXCEPT ![n] = col]
    /\ UNCHANGED <<messages, pc, sampleSet, loopsDone>>

RequireColor(p) ==
  /\ pc[p] = "waiting"
  /\ \E n \in Node : <<n, p>> \in HostMapping /\ slushColor[n] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<slushColor, messages, sampleSet, loopsDone>>

\* Loop process picks a random sample of peers and queries their colors.
QuerySample(p) ==
  /\ pc[p] = "sampling"
  /\ loopsDone[p] < SlushIterationCount
  /\ \E S \in SUBSET (Node \ {p}) : Cardinality(S) = SampleSetSize
       /\ messages' = messages \union {[kind |-> "query", src |-> p, dst |-> q, col |-> slushColor[p]] : q \in S}
       /\ sampleSet' = [sampleSet EXCEPT ![p] = S]
  /\ pc' = [pc EXCEPT ![p] = "tallying"]
  /\ UNCHANGED <<slushColor, loopsDone>>

\* A query process adopts the query's color if it is currently uncolored, then
\* replies with its (new or old) color.
RespondQuery(q) ==
  \E m \in messages :
    /\ m.kind = "query" /\ m.dst = q
    /\ slushColor' = [slushColor EXCEPT ![q] = IF slushColor[q] = NoColor THEN m.col ELSE slushColor[q]]
    /\ messages' = (messages \ {m}) \union {[kind |-> "reply", src |-> q, dst |-> m.src, col |-> slushColor[q]]}
    /\ UNCHANGED <<pc, sampleSet, loopsDone>>

\* The loop flips its color only if a color reaches the flip threshold.
TallyReplies(p) ==
  /\ pc[p] = "tallying"
  /\ \A n \in sampleSet[p] : \E m \in messages : m.kind = "reply" /\ m.src = n /\ m.dst = p
  /\ LET cc[g \in {0, 1}] ==
         Cardinality({n \in sampleSet[p] : \E m \in messages : m.kind = "reply" /\ m.src = n /\ m.col = g})
     IN
       /\ IF \E g \in {0, 1} : cc[g] >= PickFlipThreshold
          THEN slushColor' = [slushColor EXCEPT ![p] = CHOOSE g \in {0, 1} : cc[g] >= PickFlipThreshold]
          ELSE slushColor' = slushColor
  /\ messages' = {m \in messages : ~(m.kind = "reply" /\ m.dst = p)}
  /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
  /\ loopsDone' = [loopsDone EXCEPT ![p] = @ + 1]
  /\ pc' = [pc EXCEPT ![p] = IF loopsDone[p] + 1 = SlushIterationCount THEN "done" ELSE "sampling"]

LoopTermination(p) ==
  /\ pc[p] = "done" /\ loopsDone[p] = SlushIterationCount
  /\ \A q \in Node : [kind |-> "term", src |-> p, dst |-> q] \notin messages
  /\ messages' = messages \union {[kind |-> "term", src |-> p, dst |-> q] : q \in Node}
  /\ UNCHANGED <<slushColor, pc, sampleSet, loopsDone>>

QueryLoopExit(q) ==
  /\ pc[q] = "replies"
  /\ \A p \in SlushLoopProcess : [kind |-> "term", src |-> p, dst |-> q] \in messages
  /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<slushColor, messages, sampleSet, loopsDone>>

Next ==
  \/ AssignColor
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : QuerySample(p)
  \/ \E q \in SlushQueryProcess : RespondQuery(q)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : LoopTermination(p)
  \/ \E q \in SlushQueryProcess : QueryLoopExit(q)

Spec == Init /\ [][Next]_<<slushColor, messages, pc, sampleSet, loopsDone>>

Termination ==
  \A p \in SlushLoopProcess \union SlushQueryProcess : <>(pc[p] = "done")

====