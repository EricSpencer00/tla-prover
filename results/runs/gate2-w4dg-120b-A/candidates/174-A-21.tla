---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

Message == [kind: {"query", "reply", "term"}, from: SlushLoopProcess \cup SlushQueryProcess, to: SlushLoopProcess \cup SlushQueryProcess, payload: {NoMessage} \cup {NoColor} \cup Node]

VARIABLES
  color, messages, pc, sample, iterCount

vars == <<color, messages, pc, sample, iterCount>>

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \cup Node]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"clientReq"} -> {"waitColor", "query", "tally", "done"]}
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"clientReq"} |-> "waitColor"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iterCount = [p \in SlushLoopProcess |-> 0]

\* The client process assigns an initial color to an uncolored node.
ClientAssignColor ==
  /\ pc["clientReq"] = "waitColor"
  /\ \E n \in Node :
       /\ color[n] = NoColor
       /\ \E c \in Node :
            /\ c # n
            /\ color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["clientReq"] = "waitColor"]
  /\ UNCHANGED <<messages, sample, iterCount>>

\* A loop process waits for its host node to be assigned a color.
RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waitColor"
       /\ \E n \in Node :
            /\ <<p, n>> \in HostMapping
            /\ color[n] # NoColor
            /\ pc' = [pc EXCEPT ![p] = "query"]
  /\ UNCHANGED <<color, messages, sample, iterCount>>

\* A loop process queries a random sample of peers for their colors; always available.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "query"
       /\ sample' = [sample EXCEPT ![p] = CHOOSE s \in SUBSET SlushQueryProcess : Cardinality(s) = SampleSetSize]
       /\ messages' = messages \cup { [kind |-> "query", from |-> p, to |-> q, payload |-> color[CHOOSE n \in Node : <<p, n>> \in HostMapping]] : q \in sample[p] }
  /\ UNCHANGED <<color, pc, iterCount>>

\* A query process replies to a query and adopts the query's color if currently uncolored.
RespondToQuery ==
  /\ \E q \in SlushQueryProcess :
       /\ \E m \in messages :
            /\ m.kind = "query"
            /\ m.to = q
            /\ LET host == CHOOSE n \in Node : <<m.from, n>> \in HostMapping IN
                 /\ color' = [color EXCEPT ![host] = IF color[host] = NoColor THEN m.payload ELSE color[host]]
                 /\ messages' = (messages \ {m}) \cup {[kind |-> "reply", from |-> q, to |-> m.from, payload |-> color[host]]}
  /\ UNCHANGED <<pc, sample, iterCount>>

\* Once all replies for the current sample are heard, the loop process tallies them; a
\* color meeting the flip threshold is adopted. Only the tally step needs fairness.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ \E m \in messages :
            /\ m.kind = "reply"
            /\ m.to = p
            /\ m.from \in sample[p]
            /\ pc[p] = "query"
            /\ UNCHANGED <<color, messages, sample, iterCount>>
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "query"
       /\ \A q \in sample[p] : [kind |-> "reply", from |-> q, to |-> p, payload |-> color[CHOOSE n \in Node : <<p, n>> \in HostMapping]] \in messages
       /\ LET counts == {c \in Node : Cardinality({q \in sample[p] : color[CHOOSE n \in Node : <<q, n>> \in HostMapping] = c}) >= PickFlipThreshold}
            /\ newColor == IF counts = {} THEN NoColor ELSE CHOOSE c \in counts : TRUE
            /\ host == CHOOSE n \in Node : <<p, n>> \in HostMapping
          IN
            /\ color' = [color EXCEPT ![host] = IF newColor = NoColor THEN color[host] ELSE newColor]
            /\ messages' = messages \ { [kind |-> "reply", from |-> q, to |-> p, payload |-> color[CHOOSE n \in Node : <<q, n>> \in HostMapping]] : q \in sample[p] }
            /\ sample' = [sample EXCEPT ![p] = {}]
            /\ iterCount' = [iterCount EXCEPT ![p] = IF iterCount[p] < SlushIterationCount THEN iterCount[p] + 1 ELSE iterCount[p]]
            /\ pc' = IF iterCount[p] < SlushIterationCount THEN [pc EXCEPT ![p] = "query"] ELSE [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<pc>>

\* A loop process that completed all iterations broadcasts a termination message.
LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "done"
       /\ messages' = messages \cup { [kind |-> "term", from |-> p, to |-> p, payload |-> NoMessage] }
  /\ UNCHANGED <<color, pc, sample, iterCount>>

\* A query process exits once every loop process has sent a termination message.
QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "waitColor"
       /\ \A p \in SlushLoopProcess : [kind |-> "term", from |-> p, to |-> p, payload |-> NoMessage] \in messages
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, messages, sample, iterCount>>

Next ==
  \/ ClientAssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTerminate
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
          /\ WF_vars(TallyReplies)

\* Every process eventually reaches its done state.
Termination ==
  \A p \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[p] = "done")

====