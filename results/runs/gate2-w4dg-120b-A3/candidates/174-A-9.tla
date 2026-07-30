---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Color assignment per node; NoColor denotes an uncolored node.
ColorOf == [n \in Node |-> NoColor]

\* Phases of the pluscal-like protocol, used as per-process program counters.
\* Each loop process also tracks which peers it sampled, and how many
\* iterations of the Slush loop it has completed.
Phases == {"assigning", "querying", "tallying", "iterating", "final"}

VARIABLES colorOf, messages, pc, sample, iter

vars == <<colorOf, messages, pc, sample, iter>>

ReplyCount(col, msgs) ==
  Cardinality({m \in msgs : m.kind = "queryReply" /\ m.target = col})

TypeInvariant ==
  /\ colorOf \in [Node -> {NoColor} \cup SlushLoopProcess]
  /\ messages \subseteq [kind : {"query", "queryReply", "termination"},
                         src : {SlushLoopProcess, SlushQueryProcess}, target : {SlushLoopProcess, SlushQueryProcess}]
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> Phases]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ colorOf = ColorOf
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "assigning"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iter = [p \in SlushLoopProcess |-> 0]

\* A client process assigns an initial color to an uncolored node.
AssignColor(n, col) ==
  /\ pc["client"] = "assigning"
  /\ colorOf[n] = NoColor
  /\ colorOf' = [colorOf EXCEPT ![n] = col]
  /\ pc' = IF \A m \in Node : colorOf[m] # NoColor THEN [pc EXCEPT !["client"] = "final"]
            ELSE pc
  /\ UNCHANGED <<messages, sample, iter>>

\* Each loop process waits for its host node to be assigned a color.
RequireColor(p) ==
  /\ pc[p] = "assigning"
  /\ colorOf[p] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "querying"]
  /\ UNCHANGED <<colorOf, messages, sample, iter>>

\* The loop process selects a random sample of the other nodes' query processes
\* and sends each a query message carrying its current color.
QuerySampleSet(p, peers) ==
  /\ pc[p] = "querying"
  /\ \E peers \in SUBSET SlushQueryProcess :
       /\ peers \neq {}
       /\ Cardinality(peers) = SampleSetSize
       /\ ~(\E q \in peers : q = p) /\ sample' = [sample EXCEPT ![p] = peers]
  /\ messages' = messages \cup {[kind |-> "query", src |-> p, target |-> q] : q \in peers}
  /\ pc' = [pc EXCEPT ![p] = "tallying"]
  /\ UNCHANGED <<colorOf, iter>>

\* A query process receives a query and, if its host node is uncolored, adopts
\* the query color before replying with its current color.
RespondToQuery(q, p) ==
  /\ pc[q] = "querying"
  /\ <<p, q>> \in HostMapping
  /\ [kind |-> "query", src |-> p, target |-> q] \in messages
  /\ colorOf' = [colorOf EXCEPT ![q] = IF colorOf[q] = NoColor THEN colorOf[p] ELSE colorOf[q]]
  /\ messages' = (messages \ {[kind |-> "query", src |-> p, target |-> q]})
                 \cup {[kind |-> "queryReply", src |-> q, target |-> p]}
  /\ UNCHANGED <<pc, sample, iter>>

\* The loop process waits for replies from the entire sample and adopts a flip
\* threshold threshold's worth of one color if it is present.
TallyReplies(p) ==
  /\ pc[p] = "tallying"
  /\ \A q \in sample[p] : [kind |-> "queryReply", src |-> q, target |-> p] \in messages
  /\ LET replies == {m \in messages : m.kind = "queryReply" /\ m.target = p}
         co1 == ReplyCount(SlushLoopProcess, replies)
         co2 == ReplyCount(SlushQueryProcess, replies)
     IN colorOf' = [colorOf EXCEPT ![p] =
          IF co1 >= PickFlipThreshold THEN SlushLoopProcess
          ELSE IF co2 >= PickFlipThreshold THEN SlushQueryProcess
          ELSE colorOf[p]]
  /\ iter' = [iter EXCEPT ![p] = iter[p] + 1]
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ pc' = IF iter[p] < SlushIterationCount THEN "iterating" ELSE "final"
  /\ UNCHANGED messages

\* Loop process iterates after a round, or broadcasts termination when done.
IterateOrTerminate(p) ==
  /\ pc[p] \in {"iterating", "final"}
  /\ IF pc[p] = "iterating"
       THEN \E peers \in SUBSET SlushQueryProcess :
              /\ peers \neq {}
              /\ Cardinality(peers) = SampleSetSize
              /\ ~(\E q \in peers : q = p) /\ sample' = [sample EXCEPT ![p] = peers]
              /\ messages' = messages \cup {[kind |-> "query", src |-> p, target |-> q] : q \in peers}
              /\ pc' = [pc EXCEPT ![p] = "tallying"]
       ELSE /\ messages' = messages \cup {[kind |-> "termination", src |-> p, target |-> "client"]}
            /\ pc' = [pc EXCEPT ![p] = "final"]
  /\ UNCHANGED <<colorOf, iter>>

\* A query process exits its reply loop once all loop processes have terminated.
QueryLoopExit(q) ==
  /\ pc[q] = "querying"
  /\ \A p \in SlushLoopProcess : [kind |-> "termination", src |-> p, target |-> "client"] \in messages
  /\ pc' = [pc EXCEPT ![q] = "final"]
  /\ UNCHANGED <<colorOf, messages, sample, iter>>

Next ==
  \/ \E n \in Node, col \in SlushLoopProcess : AssignColor(n, col)
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess, peers \in SUBSET SlushQueryProcess : QuerySampleSet(p, peers)
  \/ \E q \in SlushQueryProcess, p \in SlushLoopProcess : RespondToQuery(q, p)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : IterateOrTerminate(p)
  \/ \E q \in SlushQueryProcess : QueryLoopExit(q)

Spec == Init /\ [][Next]_vars

\* Slush is a metastable (convergent) protocol, so the only thing that can be
\* proved here is termination of all processes; convergence to a single color
\* is a probabilistic property that TLA+ cannot express.
Properties == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "final")

====