---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* HostMapping is the set of (node, loop process, query process) triples that
\* pair each node with its two associated processes.
Nodes == Node
LoopProcesses == SlushLoopProcess
QueryProcesses == SlushQueryProcess
LoopFor(n) == CHOOSE l \in LoopProcesses : \E q \in QueryProcesses : <<n, l, q>> \in HostMapping
QueryFor(n) == CHOOSE q \in QueryProcesses : \E l \in LoopProcesses : <<n, l, q>> \in HostMapping

ColorSpace == {"color1", "color2"}

VARIABLES assign, messages, pc, sample, iteration

vars == << assign, messages, pc, sample, iteration >>

QueryMessage == [dest: QueryProcesses, src: LoopProcesses, col: ColorSpace]
QueryReply == [dest: LoopProcesses, src: QueryProcesses, col: ColorSpace]
TerminationMessage == [dest: LoopProcesses, kind: {"termination"}]

StateSpace == QueryMessage \cup QueryReply \cup TerminationMessage \cup {NoMessage}

TypeOK ==
  /\ assign \in [Nodes -> ColorSpace \cup {NoColor}]
  /\ messages \subseteq StateSpace
  /\ pc \in [LoopProcesses \cup QueryProcesses \cup {clientRequest} -> {"waiting", "done"}]
  /\ sample \in [LoopProcesses -> SUBSET QueryProcesses]
  /\ iteration \in [LoopProcesses -> 0..SlushIterationCount]

Init ==
  /\ assign = [n \in Nodes |-> NoColor]
  /\ messages = {}
  /\ sample = [l \in LoopProcesses |-> {}]
  /\ iteration = [l \in LoopProcesses |-> 0]
  /\ pc = [p \in LoopProcesses \cup QueryProcesses \cup {clientRequest} |-> "waiting"]

\* A client process assigns an uncolored node a random color, representing an
\* external transaction arriving at the network.
ClientAssignColor ==
  /\ pc[clientRequest] = "waiting"
  /\ \E n \in Nodes, col \in ColorSpace :
       /\ assign[n] = NoColor
       /\ assign' = [assign EXCEPT ![n] = col]
  /\ pc' = [pc EXCEPT ![clientRequest] = "done"]
  /\ UNCHANGED <<messages, sample, iteration>>

RequireColor ==
  /\ \E l \in LoopProcesses :
       /\ pc[l] = "waiting"
       /\ assign[CHOOSE n \in Nodes : LoopFor(n) = l] # NoColor
       /\ pc' = [pc EXCEPT ![l] = "doing"]
  /\ UNCHANGED <<assign, messages, sample, iteration>>

\* A loop process samples a random subset of peers and sends a query message to
\* each sampled peer's query process. The sample size is fixed.
QuerySampleSet ==
  /\ \E l \in LoopProcesses :
       /\ pc[l] = "doing"
       /\ iteration[l] < SlushIterationCount
       /\ sample[l] = {}
       /\ \E sub \in SUBSET QueryProcesses :
            /\ Cardinality(sub) = SampleSetSize
            /\ sample' = [sample EXCEPT ![l] = sub]
            /\ messages' = messages \cup { [dest |-> q, src |-> l, col |-> assign[CHOOSE n \in Nodes : LoopFor(n) = l]] : q \in sub }
  /\ UNCHANGED <<assign, pc, iteration>>

\* A query process records the reply, adopting the query's color only if it is
\* currently uncolored; it then replies back to the loop process.
RespondToQuery ==
  /\ \E m \in QueryMessage :
       /\ m \in messages
       /\ assign[CHOOSE n \in Nodes : QueryFor(n) = m.dest] = NoColor
       /\ assign' = [assign EXCEPT ![CHOOSE n \in Nodes : QueryFor(n) = m.dest] = m.col]
       /\ messages' = (messages \ {m}) \cup { [dest |-> m.src, src |-> m.dest, col |-> assign[CHOOSE n \in Nodes : QueryFor(n) = m.dest]] }
  /\ UNCHANGED <<pc, sample, iteration>>

\* The loop process tallies replies; if one color reaches the flip threshold the
\* node adopts it.
TallyReplies ==
  /\ \E l \in LoopProcesses :
       /\ pc[l] = "doing"
       /\ sample[l] # {}
       /\ \A q \in sample[l] : [dest |-> l, src |-> q, col |-> assign[CHOOSE n \in Nodes : QueryFor(n) = q]] \in messages
       /\ LET replies == { [dest |-> l, src |-> q, col |-> assign[CHOOSE n \in Nodes : QueryFor(n) = q]] : q \in sample[l] }
              colCount(col) == Cardinality({ m \in replies : m.col = col })
              winner == CHOOSE col \in ColorSpace : colCount(col) >= PickFlipThreshold
          IN assign' = [assign EXCEPT ![CHOOSE n \in Nodes : LoopFor(n) = l] = winner]
       /\ messages' = messages \ replies
       /\ sample' = [sample EXCEPT ![l] = {}]
       /\ iteration' = [iteration EXCEPT ![l] = @ + 1]
  /\ UNCHANGED pc

LoopTermination ==
  /\ \E l \in LoopProcesses :
       /\ pc[l] = "doing"
       /\ iteration[l] = SlushIterationCount
       /\ pc' = [pc EXCEPT ![l] = "done"]
       /\ messages' = messages \cup { [dest |-> l, kind |-> "termination"] }
  /\ UNCHANGED <<assign, sample, iteration>>

QueryLoopExit ==
  /\ \A l \in LoopProcesses : [dest |-> l, kind |-> "termination"] \in messages
  /\ \A q \in QueryProcesses : pc[q] = "waiting"
  /\ pc' = [q \in QueryProcesses |-> "done"]
  /\ UNCHANGED <<assign, messages, sample, iteration>>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

AllProcessesTerminate == <>(\A l \in LoopProcesses \cup QueryProcesses \cup {clientRequest} : pc[l] = "done")

====