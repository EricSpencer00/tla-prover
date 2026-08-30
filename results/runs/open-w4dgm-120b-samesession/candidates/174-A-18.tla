---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Types: Color (color on each node or uncolored), Message (query, reply, or termination),
\* Phase (where each concurrent process is in its bounded execution), SampleSet (the peers
\* a loop process queried in the current round), and Iterations (how many rounds a loop
\* process has completed).
Message == [kind: {"query", "reply", "terminate"}, target: SlushLoopProcess, source: SlushQueryProcess \cup SlushLoopProcess, content: {NoColor} \cup (Node \X {"a", "b"})]
Color == {NoColor} \cup (Node \X {"a", "b"})

VARIABLES assignment, messages, phase, sampleSet, iterations

TypeOK ==
  /\ assignment \in [Node -> Color]
  /\ messages \subseteq Message
  /\ phase \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"waiting", "ready", "reporting", "replied", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

vars == <<assignment, messages, phase, sampleSet, iterations>>

Init ==
  /\ assignment = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ phase = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> IF p = "client" THEN "ready" ELSE "waiting"]
  /\ sampleSet = [l \in SlushLoopProcess |-> {}]
  /\ iterations = [l \in SlushLoopProcess |-> 0]

ClientAssignsColor ==
  /\ phase["client"] = "ready"
  /\ \E n \in Node, c \in {"a", "b"} :
       /\ assignment[n] = NoColor
       /\ assignment' = [assignment EXCEPT ![n] = <<n, c>>]
  /\ UNCHANGED <<messages, phase, sampleSet, iterations>>

RequireColor ==
  /\ \E l \in SlushLoopProcess :
       /\ phase[l] = "waiting"
       /\ LET n == CHOOSE n \in Node : <<l, n>> \in HostMapping
          IN \/ assignment[n] # NoColor
             /\ phase' = [phase EXCEPT ![l] = "ready"]
  /\ UNCHANGED <<assignment, messages, sampleSet, iterations>>

QuerySampleSet ==
  /\ \E l \in SlushLoopProcess :
       /\ phase[l] = "ready"
       /\ LET n == CHOOSE n \in Node : <<l, n>> \in HostMapping
              pairs == SAMPLE(SubSetOfSeq(HostMapping), SampleSetSize)
              qprocs == {q \in SlushQueryProcess : \E x \in pairs : <<x, n>> \in HostMapping}
          IN /\ sampleSet' = [sampleSet EXCEPT ![l] = qprocs]
             /\ messages' = messages \cup {[kind |-> "query", target |-> l, source |-> q, content |-> assignment[n]] : q \in qprocs}
             /\ phase' = [phase EXCEPT ![l] = "reporting"]
  /\ UNCHANGED <<assignment, iterations>>

\* A query process adopts the query's color if it is uncolored, then replies.
RespondQuery ==
  /\ \E m \in messages :
       /\ m.kind = "query"
       /\ LET q == m.source
              n == CHOOSE n \in Node : <<q, n>> \in HostMapping
          IN /\ (assignment[n] = NoColor
                 /\ assignment' = [assignment EXCEPT ![n] = m.content])
             /\ messages' = (messages \ {m}) \cup {[kind |-> "reply", target |-> m.target, source |-> q, content |-> assignment[n]]}
  /\ UNCHANGED <<phase, sampleSet, iterations>>

TallyReplies ==
  /\ \E l \in SlushLoopProcess :
       /\ phase[l] = "reporting"
       /\ LET replies == {m \in messages : m.kind = "reply" /\ m.target = l}
              tally(c) == Cardinality({m \in replies : m.content = c})
              nc == CHOOSE n \in Node : <<l, n>> \in HostMapping
          IN /\ \E c \in {"a", "b"} : tally(c) >= PickFlipThreshold /\ assignment' = [assignment EXCEPT ![nc] = <<nc, c>>]
             /\ messages' = messages \ replies
             /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
             /\ iterations' = [iterations EXCEPT ![l] = @ + 1]
             /\ phase' = IF iterations[l] + 1 >= SlushIterationCount THEN "done" ELSE "ready"
  /\ UNCHANGED <<>>

LoopTerminate ==
  /\ \E l \in SlushLoopProcess :
       /\ phase[l] = "done"
       /\ ~(\E m \in messages : m.kind = "terminate" /\ m.target = l)
       /\ messages' = messages \cup {[kind |-> "terminate", target |-> l, source |-> l, content |-> NoColor]}
  /\ UNCHANGED <<assignment, phase, sampleSet, iterations>>

QueryLoopExit ==
  /\ \A q \in SlushQueryProcess : phase[q] = "waiting"
  /\ \A l \in SlushLoopProcess : \A m \in messages : ~(m.kind = "terminate" /\ m.target = l)
  /\ phase' = [phase EXCEPT ![q] = "done" : q \in SlushQueryProcess]
  /\ UNCHANGED <<assignment, messages, sampleSet, iterations>>

Next == ClientAssignsColor \/ RequireColor \/ QuerySampleSet \/ RespondQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignsColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit)

TypeInvariant ==
  /\ assignment \in [Node -> Color]
  /\ \A m \in messages : m.kind \in {"query", "reply", "terminate"}

Termination == \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : <>(phase[p] = "done")

====