---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* A message is a tuple: (kind, src, dst, payload). kind is one of
\* "query", "reply", or "term". payload is a color for query/reply,
\* and NoMessage for termination messages.
Message == [kind: {"query", "reply", "term"},
            src: SlushLoopProcess \cup SlushQueryProcess,
            dst: SlushLoopProcess \cup SlushQueryProcess,
            payload: {NoMessage} \cup {NoColor} \cup Node]

VARIABLES color, msgs, pc, sample, iters

vars == <<color, msgs, pc, sample, iters>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup Node]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> 0..3]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> 0]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node.
ClientAssign ==
  /\ pc["client"] = 0
  /\ \E n \in Node :
       /\ color[n] = NoColor
       /\ \E c \in Node : color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = 1]
  /\ UNCHANGED <<msgs, sample, iters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 0
       /\ \E n \in Node :
            /\ <<n, p, "loop">> \in HostMapping
            /\ color[n] # NoColor
            /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<color, msgs, sample, iters>>

\* The loop process samples a random set of peers and queries them.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ iters[p] < SlushIterationCount
       /\ \E peers \in SUBSET SlushQueryProcess :
            /\ peers # {}
            /\ Cardinality(peers) = SampleSetSize
            /\ sample' = [sample EXCEPT ![p] = peers]
            /\ msgs' = msgs \cup
                 {[kind |-> "query", src |-> p, dst |-> q,
                   payload |-> color[CHOOSE n \in Node : <<n, p, "loop">> \in HostMapping]]
                    : q \in peers]
       /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<color, iters>>

\* A query process adopts the query's color if uncolored, then replies.
RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.kind = "query"
       /\ \E n \in Node :
            /\ <<n, m.dst, "query">> \in HostMapping
            /\ color' = IF color[n] = NoColor THEN [color EXCEPT ![n] = m.payload]
                        ELSE color
            /\ msgs' = (msgs \ {m}) \cup
                 {[kind |-> "reply", src |-> m.dst, dst |-> m.src,
                   payload |-> color[CHOOSE x \in Node : <<x, m.dst, "query">> \in HostMapping]]}
       /\ UNCHANGED <<pc, sample, iters>>

\* The loop process tallies replies and flips its node's color if a
\* color reaches the flip threshold.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 2
       /\ \A q \in sample[p] : \E m \in msgs : m.kind = "reply" /\ m.src = q /\ m.dst = p
       /\ LET replies == {m.payload : m \in {x \in msgs : x.kind = "reply" /\ x.dst = p}}
              cnt(c) == Cardinality({m \in msgs : m.kind = "reply" /\ m.dst = p /\ m.payload = c})
          IN
            /\ \E c \in replies : cnt(c) >= PickFlipThreshold
                 /\ color' = [color EXCEPT ![CHOOSE n \in Node : <<n, p, "loop">> \in HostMapping] = c]
            /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
            /\ sample' = [sample EXCEPT ![p] = {}]
            /\ msgs' = {m \in msgs : ~(m.kind = "reply" /\ m.dst = p)}
            /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<color>>

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ iters[p] = SlushIterationCount
       /\ msgs' = msgs \cup {[kind |-> "term", src |-> p, dst |-> "client", payload |-> NoMessage]}
       /\ pc' = [pc EXCEPT ![p] = 3]
  /\ UNCHANGED <<color, sample, iters>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = 0
       /\ \A p \in SlushLoopProcess : [kind |-> "term", src |-> p, dst |-> "client", payload |-> NoMessage] \in msgs
       /\ pc' = [pc EXCEPT ![q] = 3]
  /\ UNCHANGED <<color, msgs, sample, iters>>

Next ==
  \/ ClientAssign \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssign) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)
        /\ WF_vars(QueryLoopExit)

Termination ==
  \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : <>(pc[p] = 3)

====