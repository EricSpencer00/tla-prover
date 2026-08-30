---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Two polls against two loop processes that vote for different colors are what
\* would make the network flip back and forth -- so the flip threshold is the
\* whole point of convergence, not the sample size itself.
NodeCount == Cardinality(Node)
LoopCount == Cardinality(SlushLoopProcess)
QueryCount == Cardinality(SlushQueryProcess)
HostOf(n, t) == \E m \in HostMapping : m[1] = n /\ m[t] = t

MessageType == [kind: {"query", "reply", "end"}, from: SlushQueryProcess,
                to: SlushLoopProcess, col: {NoMessage} \union {"red", "blue"}]

VARIABLES color, inbox, pc, sample, iterations

TypeOK ==
  /\ color \in [Node -> {NoColor} \union {"red", "blue"}]
  /\ inbox \subseteq MessageType
  /\ pc \in [SlushLoopProcess -> {"waiting", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [t \in SlushLoopProcess |-> "waiting"]
  /\ sample = [t \in SlushLoopProcess |-> {}]
  /\ iterations = [t \in SlushLoopProcess |-> 0]

\* Client transactions arrive here, so the network is never empty.
AssignColor(n) ==
  /\ color[n] = NoColor
  /\ color' = [color EXCEPT ![n] = CHOOSE c \in {"red", "blue"} : TRUE]
  /\ UNCHANGED <<inbox, pc, sample, iterations>>

\* A loop process is blocked until its host node has been assigned a color.
RequireColor(t) ==
  /\ pc[t] = "waiting"
  /\ \E n \in Node : HostOf(n, t) /\ color[n] # NoColor
  /\ pc' = [pc EXCEPT ![t] = "sampling"]
  /\ UNCHANGED <<color, inbox, sample, iterations>>

QuerySampleSet(t) ==
  /\ pc[t] = "sampling"
  /\ sample[t] = {}
  /\ Cardinality(inbox) < 2 * NodeCount
  /\ \E Q \in SUBSET SlushQueryProcess :
       /\ Cardinality(Q) = SampleSetSize
       /\ sample' = [sample EXCEPT ![t] = Q]
       /\ inbox' = inbox \union
            { [kind |-> "query", from |-> q, to |-> t,
               col |-> color[HostOf(^, q)]] : q \in Q }
  /\ UNCHANGED <<color, pc, iterations>>

\* A query is answered synchronously: the node adopts the query's color if it
\* has none, then replies with its current color.
RespondToQuery(m) ==
  /\ m.kind = "query"
  /\ m \in inbox
  /\ inbox' = (inbox \ {m}) \union
       {[kind |-> "reply", from |-> m.from, to |-> m.to, col |->
            IF color[HostOf(^, m.from)] = NoColor
              THEN m.col ELSE color[HostOf(^, m.from)]]}
  /\ UNCHANGED <<color, pc, sample, iterations>>

TallyReplies(t) ==
  /\ pc[t] = "sampling"
  /\ Cardinality(sample[t]) = SampleSetSize
  /\ Cardinality({m \in inbox : m.kind = "reply" /\ m.to = t}) = SampleSetSize
  /\ Cardinality({m \in inbox : m.kind = "reply" /\ m.to = t /\ m.col = "red"}) >= PickFlipThreshold
       \/ Cardinality({m \in inbox : m.kind = "reply" /\ m.to = t /\ m.col = "blue"}) >= PickFlipThreshold
  /\ color' = [color EXCEPT ![HostOf(^, t)] =
        IF Cardinality({m \in inbox : m.kind = "reply" /\ m.to = t /\ m.col = "red"}) >= PickFlipThreshold
          THEN "red" ELSE "blue"]
  /\ inbox' = inbox \ {[m \in inbox : m.kind = "reply" /\ m.to = t] \union
                         {[kind |-> "query", from |-> q, to |-> t,
                            col |-> color[HostOf(^, q)]] : q \in sample[t]}}
  /\ sample' = [sample EXCEPT ![t] = {}]
  /\ iterations' = [iterations EXCEPT ![t] = @ + 1]
  /\ pc' = [pc EXCEPT ![t] = "tallying"]

\* The loop process is done once every iteration is used up.
LoopTermination(t) ==
  /\ pc[t] \in {"sampling", "tallying"}
  /\ iterations[t] = SlushIterationCount
  /\ Cardinality(inbox) < 2 * NodeCount
  /\ pc' = [pc EXCEPT ![t] = "done"]
  /\ inbox' = inbox \union
       {[kind |-> "end", from |-> NoMessage, to |-> t, col |-> NoMessage]}
  /\ UNCHANGED <<color, sample, iterations>>

QueryLoopExit ==
  /\ \A t \in SlushLoopProcess : pc[t] = "done"
  /\ Cardinality(inbox) < 2 * NodeCount
  /\ inbox' = inbox \union
       {[kind |-> "end", from |-> NoMessage, to |-> t, col |-> NoMessage}
        : t \in SlushLoopProcess}
  /\ UNCHANGED <<color, pc, sample, iterations>>

Next ==
  \/ \E n \in Node : AssignColor(n)
  \/ \E t \in SlushLoopProcess : RequireColor(t) \/ TallyReplies(t) \/ LoopTermination(t)
  \/ \E m \in inbox : RespondToQuery(m)
  \/ \E t \in SlushLoopProcess : QuerySampleSet(t)
  \/ QueryLoopExit

Spec ==
  /\ Init
  /\ [][Next]_<<color, inbox, pc, sample, iterations>>
  /\ \A m \in MessageType : SF_vars(RespondToQuery(m))
  /\ \A t \in SlushLoopProcess : WF_vars(QuerySampleSet(t))
  /\ \A t \in SlushLoopProcess : WF_vars(TallyReplies(t))

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \union {"red", "blue"}]
  /\ inbox \subseteq MessageType
  /\ pc \in [SlushLoopProcess -> {"waiting", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Termination == \A t \in SlushLoopProcess : <>(pc[t] = "done")

====