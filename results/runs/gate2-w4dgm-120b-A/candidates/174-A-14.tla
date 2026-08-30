---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* The Slush protocol: each node runs a loop process that samples a set of     *)
(* peers and adopts a popular opinion, and a query process that answers         *)
(* queries.  TLA+ cannot model the random sampling itself, so the sample       *)
(* set is nondeterministically chosen from all peers; this keeps the spec       *)
(* executable while preserving the shape of the action.                         *)

CONSTANTS
  Node,                 \* the set of all nodes in the network
  SlushLoopProcess,     \* the set of loop processes, one per node
  SlushQueryProcess,    \* the set of query processes, one per node
  HostMapping,          \* set of <<node, loopProc, queryProc>> linking the three
  SlushIterationCount,  \* bounded number of iterations each loop process runs
  SampleSetSize,        \* how many peers are sampled in each round
  PickFlipThreshold,    \* replies needed for the node to adopt a color
  NoColor,              \* the uncolored sentinel value
  NoMessage             \* the "no reply yet" sentinel value

RECURSIVE SumOverFn(_, _)
SumOverFn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOverFn(f, S \ {x})

VARIABLES color, messages, pc, sampleSet, iterations

vars == <<color, messages, pc, sampleSet, iterations>>

\* Each node has exactly one loop process and one query process.
\* The host function extracts that pairing from the declared mapping.
HostOf(p) == CHOOSE r \in HostMapping : r[2] = p
QueryOf(p) == CHOOSE r \in HostMapping : r[3] = p
QueryProcOf(n) == CHOOSE r \in HostMapping : r[1] = n /\ r[3]

MessageType == [kind: {"query", "reply", "terminate"}, from: Node, to: Node,
                body: {NoColor} \union {"red", "blue"}]

TypeOK ==
  /\ color \in [Node -> {NoColor, "red", "blue"}]
  /\ messages \subseteq MessageType
  /\ pc \in [SlushLoopProcess -> {"init", "waiting", "tallying", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess |-> "init"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterations = [p \in SlushLoopProcess |-> 0]

\* The client hands out the first color each node receives, one at a time.
AssignColor ==
  \E n \in Node, col \in {"red", "blue"} :
    /\ color[n] = NoColor
    /\ color' = [color EXCEPT ![n] = col]
    /\ UNCHANGED <<messages, pc, sampleSet, iterations>>

RequireColor ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "init"
    /\ color[HostOf(p)] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<color, messages, sampleSet, iterations>>

NondeterministicSample(p) ==
  LET peers == {q \in SlushQueryProcess : q # QueryOf(p)} IN
  {q \in peers : Cardinality({w \in peers : w <= q}) <= SampleSetSize}

QuerySampleSet ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "waiting"
    /\ iterations[p] < SlushIterationCount
    /\ sampleSet' = [sampleSet EXCEPT ![p] = NondeterministicSample(p)]
    /\ messages' = messages \union
         {[kind |-> "query", from |-> HostOf(p), to |-> HostOf(q),
           body |-> color[HostOf(p)]] : q \in NondeterministicSample(p)}
    /\ pc' = [pc EXCEPT ![p] = "tallying"]
    /\ UNCHANGED <<color, iterations>>

RespondToQuery ==
  \E msg \in messages :
    /\ msg.kind = "query"
    /\ LET n == msg.to IN
       /\ color' = [color EXCEPT ![n] =
                     IF color[n] = NoColor THEN msg.body ELSE color[n]]
       /\ messages' = (messages \ {msg})
            \union {[kind |-> "reply", from |-> n, to |-> msg.from, body |-> color[n]]}
    /\ UNCHANGED <<pc, sampleSet, iterations>>

TallyReplies ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "tallying"
    /\ \A q \in sampleSet[p] : \E m \in messages :
         /\ m.kind = "reply"
         /\ m.from = HostOf(q)
         /\ m.to = HostOf(p)
    /\ LET replyColors == [c \in {"red", "blue"} |->
           Cardinality({q \in sampleSet[p] :
             \E m \in messages :
               /\ m.kind = "reply"
               /\ m.from = HostOf(q)
               /\ m.to = HostOf(p)
               /\ m.body = c})]
       count == (\E c \in {"red", "blue"} : replyColors[c])
       newColor == IF count >= PickFlipThreshold THEN "red" ELSE "blue"
       in color' = [color EXCEPT ![HostOf(p)] = newColor]
    /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
    /\ iterations' = [iterations EXCEPT ![p] = iterations[p] + 1]
    /\ pc' = IF iterations[p] + 1 = SlushIterationCount
              THEN "done"
              ELSE "waiting"
    /\ UNCHANGED messages

LoopTerminate ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "done"
    /\ \A msg \in messages : ~(msg.kind = "terminate" /\ msg.from = HostOf(p))
    /\ messages' = messages \union
         {[kind |-> "terminate", from |-> HostOf(p), to |-> NoColor, body |-> NoColor]}
    /\ UNCHANGED <<color, pc, sampleSet, iterations>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess :
       \E m \in messages : m.kind = "terminate" /\ m.from = HostOf(p)
  /\ \A q \in SlushQueryProcess :
       \A msg \in messages : ~ (msg.kind = "query" /\ msg.from = HostOf(q))
  /\ UNCHANGED vars

Next ==
  \/ AssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTerminate
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ (\A p \in SlushLoopProcess : WF_vars(RequireColor))
  /\ (\A p \in SlushLoopProcess : WF_vars(NondeterministicSample(p)))
  /\ (\A p \in SlushLoopProcess : WF_vars(QuerySampleSet))
  /\ (\A p \in SlushLoopProcess : WF_vars(TallyReplies))

TypeInvariant == TypeOK

Termination == <>(\A p \in SlushLoopProcess : pc[p] = "done")

====