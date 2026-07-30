---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* A message is a tuple: [kind | from | to | payload].
\* kind = "query" (loop -> query), "reply" (query -> loop), or "term" (termination broadcast).
\* payload = the color being queried or replied with; NoMessage for termination messages.
Message == [kind: {"query", "reply", "term"}, from: SlushLoopProcess \cup SlushQueryProcess,
            to: SlushLoopProcess \cup SlushQueryProcess, payload: {NoColor} \cup {NoMessage} \cup Node]

VARIABLES color, msgs, pc, sample, iters

vars == <<color, msgs, pc, sample, iters>>

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \cup Node]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "idle"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node.
ClientAssignColor ==
  /\ pc["client"] = "idle"
  /\ \E n \in Node, c \in Node :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sample, iters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "idle"
       /\ LET n == CHOOSE n \in Node : <<p, n>> \in HostMapping
       /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<color, msgs, sample, iters>>

\* A loop process samples a random set of peers and queries their colors.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "done"
       /\ iters[p] < SlushIterationCount
       /\ sample[p] = {}
       /\ \E peers \in SUBSET SlushQueryProcess :
            /\ peers # {}
            /\ Cardinality(peers) = SampleSetSize
            /\ sample' = [sample EXCEPT ![p] = peers]
            /\ LET n == CHOOSE n \in Node : <<p, n>> \in HostMapping
               msgs' = msgs \cup {[kind |-> "query", from |-> p, to |-> q,
                                   payload |-> color[n]] : q \in peers}
  /\ UNCHANGED <<color, pc, iters>>

\* A query process adopts the query's color if uncolored, then replies.
RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.kind = "query"
       /\ LET q == m.to
          n == CHOOSE n \in Node : <<q, n>> \in HostMapping
          c == IF color[n] = NoColor THEN m.payload ELSE color[n]
          msgs' = (msgs \ {m}) \cup {[kind |-> "reply", from |-> q, to |-> m.from, payload |-> c]}
          color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<pc, sample, iters>>

\* The loop process tallies replies and flips its node's color if a majority is reached.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ sample[p] # {}
       /\ \A q \in sample[p] : \E m \in msgs : m.kind = "reply" /\ m.from = q /\ m.to = p
       /\ LET n == CHOOSE n \in Node : <<p, n>> \in HostMapping
              replies == {m.payload : m \in {x \in msgs : x.kind = "reply" /\ x.to = p}}
              count(c) == Cardinality({x \in replies : x = c})
              cmax == CHOOSE c \in replies : \A d \in replies : count(c) >= count(d)
          IN /\ IF count(cmax) >= PickFlipThreshold THEN color' = [color EXCEPT ![n] = cmax] ELSE color' = color
             msgs' = {m \in msgs : ~(m.kind = "reply" /\ m.to = p)}
             sample' = [sample EXCEPT ![p] = {}]
             iters' = [iters EXCEPT ![p] = iters[p] + 1]
  /\ UNCHANGED pc

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ iters[p] = SlushIterationCount
       /\ sample[p] = {}
       /\ pc[p] = "done"
       /\ \A m \in msgs : ~(m.kind = "query" /\ m.from = p)
       /\ msgs' = msgs \cup {[kind |-> "term", from |-> p, to |-> p, payload |-> NoMessage]}
       /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<color, sample, iters>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "idle"
       /\ \A p \in SlushLoopProcess : \E m \in msgs : m.kind = "term" /\ m.from = p
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, msgs, sample, iters>>

Next ==
  \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

Termination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "done")

====