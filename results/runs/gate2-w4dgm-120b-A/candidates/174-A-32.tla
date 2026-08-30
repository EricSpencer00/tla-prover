---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush is the simplest Snow protocol: nodes repeatedly query random peers and
\* adopt a sufficiently popular opinion.  TLA+ has no probabilistic reasoning,
\* so this is an executable model of the protocol rather than a convergence proof.

CONSTANTS
  Node,                \* the shared pool of nodes participating in Slush
  SlushLoopProcess,    \* Loop(p): p drives its host node's Slush iteration
  SlushQueryProcess,   \* Query(q): q answers query messages from loop processes
  HostMapping,         \* each process triple <p, q, n>: loop p, query q, node n
  SlushIterationCount, \* number of Slush iterations each loop process performs
  SampleSetSize,       \* fixed size of the peer sample a loop process queries
  PickFlipThreshold,   \* number of peer replies required to adopt a color
  NoColor,             \* the uncolored sentinel
  NoMessage            \* the empty-slot sentinel for a message slot

\* A message is a tuple <emitter, address, kind, datum>.  Kind determines the
\* interpretation of datum: a query carries a candidate color, a query reply
\* carries the responder's current color, and a termination carries no datum.
Message == [emitter: SlushLoopProcess, address: SlushQueryProcess,
            kind: {"query", "queryReply", "termination"}, datum: Node \cup {NoColor} \cup {NoMessage}]

VARIABLES color, message, pc, sampleSet, loopIteration

vars == <<color, message, pc, sampleSet, loopIteration>>

Loop == CHOOSE p \in SlushLoopProcess : TRUE
Query == CHOOSE q \in SlushQueryProcess : TRUE
HostOf(p) == CHOOSE n \in Node : <<p, Query, n>> \in HostMapping
NodeOf(q) == CHOOSE n \in Node : <<Loop, q, n>> \in HostMapping

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup ("c1" \cup "c2")]
  /\ message \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"wait", "sample", "tally", "done"}]
  /\ [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ message = {}
  /\ pc = [p \in SlushLoopProcess |-> "wait"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopIteration = [p \in SlushLoopProcess |-> 0]

\* A query message is always answered, so to guarantee eventual termination no
\* loop process may be stuck forever waiting for a reply to a query that was
\* never sent; both directions below are guarded by sampleSet # {}.
CollectReplies(p) ==
  \E m \in message : m.kind = "queryReply" /\ m.address = Query /\ m.emitter = p

Reply(m) ==
  /\ m \in message
  /\ m.kind = "query"
  /\ color' = [color EXCEPT ![NodeOf(m.address)] =
                 IF color[NodeOf(m.address)] = NoColor THEN m.datum ELSE color[NodeOf(m.address)]]
  /\ message' = (message \ {m}) \cup {[emitter |-> m.emitter, address |-> Query,
                                      kind |-> "queryReply", datum |-> color[NodeOf(m.address)]]}
  /\ UNCHANGED <<pc, sampleSet, loopIteration>>

CountVotes(p, c) ==
  Cardinality({m \in message : m.kind = "queryReply" /\ m.address = Query /\ m.emitter = p /\ m.datum = c})

\* A node adopts the sampled color only once a strict majority of its sampled
\* peers has replied with that same color -- the metastable "flip" step of Slush.
FlipStep(p) ==
  \/ (CountVotes(p, "c1") >= PickFlipThreshold /\ color' = [color EXCEPT ![HostOf(p)] = "c1"])
  \/ (CountVotes(p, "c2") >= PickFlipThreshold /\ color' = [color EXCEPT ![HostOf(p)] = "c2"])

Next ==
  \/ \E n \in Node : \E c \in {"c1", "c2"} : color = [color EXCEPT ![n] = c] /\ UNCHANGED <<message, pc, sampleSet, loopIteration>>
  \/ \E p \in SlushLoopProcess : pc[p] = "wait" /\ color[HostOf(p)] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "sample"]
       /\ UNCHANGED <<color, message, sampleSet, loopIteration>>
  \/ \E p \in SlushLoopProcess : pc[p] = "sample"
       /\ \E S \in SUBSET SlushQueryProcess :
            /\ Cardinality(S) = SampleSetSize
            /\ S # {}
            /\ sampleSet' = [sampleSet EXCEPT ![p] = S]
            /\ message' = message \cup
                 {[emitter |-> p, address |-> q, kind |-> "query", datum |-> color[HostOf(p)]] : q \in S}
       /\ pc' = [pc EXCEPT ![p] = "tally"]
       /\ UNCHANGED <<color loopIteration>>
  \/ \E p \in SlushLoopProcess : pc[p] = "tally" /\ CollectReplies(p)
       /\ FlipStep(p)
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ loopIteration' = [loopIteration EXCEPT ![p] = IF loopIteration[p] < SlushIterationCount
                                                        THEN loopIteration[p] + 1 ELSE loopIteration[p]]
       /\ pc' = IF loopIteration[p] + 1 >= SlushIterationCount
                THEN "done" ELSE "sample"
       /\ message' = {m \in message : ~(m.kind = "queryReply" /\ m.address = Query /\ m.emitter = p)}
       /\ UNCHANGED <<color>>
  \/ \E p \in SlushLoopProcess : pc[p] = "done" /\ ~(\E m \in message : m.kind = "termination" /\ m.emitter = p)
       /\ message' = message \cup {[emitter |-> p, address |-> Query, kind |-> "termination", datum |-> NoMessage]}
       /\ UNCHANGED <<color, pc, sampleSet, loopIteration>>
  \/ \E m \in message : Reply(m)
  \/ \E q \in SlushQueryProcess : pc[Loop] = "done" /\ pc' = [pc EXCEPT ![Loop] = "awaitTermination"]
       /\ UNCHANGED <<color, message, sampleSet, loopIteration>>

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E m \in Message : Reply(m))

TypeInvariant == TypeOK

AllProcessesDone == <>(\A p \in SlushLoopProcess : pc[p] = "done")

====