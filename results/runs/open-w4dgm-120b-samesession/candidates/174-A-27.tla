---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush is the simplest Snow-family protocol: nodes repeatedly sample random  *)
(* peers and adopt a sufficiently popular opinion, causing the network to      *)
(* converge on a single color.  This PlusCal spec is meant as executable         *)
(* pseudocode; convergence itself is probabilistic and not verifiable here.    *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A host mapping ties each node to its loop process and its query process.
\* The three sets (nodes, loop processes, query processes) must be pairwise
\* equally sized, so each node has exactly one of each partner.
HostOf(p) == CHOOSE n \in Node : << n, p, HostMapping[n] >> \in HostMapping
QueryOf(p) == HostMapping[HostOf(p)]

NodeColor == [Node -> (1..2) \cup {NoColor}]
LoopState == [pc: {"requesting", "collecting", "done"}, sample: SUBSET SlushQueryProcess, seen: [c1 : 0..Cardinality(Node), c2 : 0..Cardinality(Node)]]
QueryState == [pc: {"replying", "done"}]

Message == [q : SlushQueryProcess, target : SlushLoopProcess, kind : {"query", "reply", "done"}, guess : 1..2 \cup {NoColor}]

VARIABLES color, inbox, loop, query, iteration

vars == << color, inbox, loop, query, iteration >>

TypeOK ==
  /\ color \in NodeColor
  /\ inbox \subseteq Message
  /\ loop \in [SlushLoopProcess -> LoopState]
  /\ query \in [SlushQueryProcess -> QueryState]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ loop = [p \in SlushLoopProcess |-> [pc |-> "requesting", sample |-> {}, seen |-> [c1 |-> 0, c2 |-> 0]]]
  /\ query = [q \in SlushQueryProcess |-> [pc |-> "replying"]]
  /\ iteration = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node (one-time).
ClientAssignColor ==
  /\ \E n \in Node, kc \in 1..2 :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = kc]
  /\ UNCHANGED << inbox, loop, query, iteration >>

RequireColor(p) ==
  /\ loop[p].pc = "requesting"
  /\ color[HostOf(p)] # NoColor
  /\ loop' = [loop EXCEPT ![p].pc = "collecting"]
  /\ UNCHANGED << color, inbox, query, iteration >>

\* Send a query to each sampled peer, asking it to return its current color.
QuerySampleSet(p) ==
  /\ loop[p].pc = "collecting"
  /\ loop[p].sample = {}
  /\ iteration[p] < SlushIterationCount
  /\ \E sample \in SUBSET SlushQueryProcess :
       /\ Cardinality(sample) = SampleSetSize
       /\ loop' = [loop EXCEPT ![p].sample = sample]
       /\ inbox' = inbox \cup {[q |-> q, target |-> p, kind |-> "query", guess |-> color[HostOf(p)]] : q \in sample}
  /\ UNCHANGED << color, query, iteration >>

\* A query process adopts an uncolored node's guess before answering.
RespondToQuery ==
  \E m \in inbox :
    /\ m.kind = "query"
    /\ query[m.q].pc = "replying"
    /\ LET upd == IF color[HostOf(m.q)] = NoColor
                 THEN [color EXCEPT ![HostOf(m.q)] = m.guess]
                 ELSE color
       IN
         /\ color' = upd
         /\ inbox' = (inbox \ {m}) \cup {[q |-> m.q, target |-> m.target, kind |-> "reply", guess |-> (IF color[HostOf(m.q)] = NoColor THEN m.guess ELSE color[HostOf(m.q)])]}
  /\ UNCHANGED << loop, query, iteration >>

\* Count the replies; if one color meets the threshold, adopt it.
TallyReplies(p) ==
  /\ loop[p].pc = "collecting"
  /\ loop[p].sample # {}
  /\ \A q \in loop[p].sample : \E m \in inbox : m.kind = "reply" /\ m.target = p /\ m.q = q
  /\ \E c \in 1..2 :
       LET count == Cardinality({m \in inbox : m.kind = "reply" /\ m.target = p /\ m.guess = c})
       IN /\ count >= PickFlipThreshold
          /\ color' = [color EXCEPT ![HostOf(p)] = c]
          /\ loop' = [loop EXCEPT ![p].sample = {}]
  /\ inbox' = {m \in inbox : ~(m.kind = "reply" /\ m.target = p)}
  /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]

LoopTermination(p) ==
  /\ loop[p].pc = "collecting"
  /\ iteration[p] = SlushIterationCount
  /\ loop' = [loop EXCEPT ![p].pc = "done"]
  /\ inbox' = inbox \cup {[q |-> NoMessage, target |-> p, kind |-> "done", guess |-> NoColor]}
  /\ UNCHANGED << color, query, iteration >>

QueryLoopExit ==
  /\ \A q \in SlushQueryProcess : query[q].pc = "replying"
  /\ \A m \in inbox : m.kind # "done"
  /\ query' = [q \in SlushQueryProcess |-> [pc |-> "done"]]
  /\ UNCHANGED << color, inbox, loop, iteration >>

Next ==
  \/ ClientAssignColor
  \/ RespondToQuery
  \/ QueryLoopExit
  \/ \E p \in SlushLoopProcess :
       RequireColor(p) \/ QuerySampleSet(p) \/ TallyReplies(p) \/ LoopTermination(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RespondToQuery)

TypeInvariant == TypeOK

AllDone == (\A p \in SlushLoopProcess : loop[p].pc = "done") /\ (\A q \in SlushQueryProcess : query[q].pc = "done")

Termination == AllDone

====