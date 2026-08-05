---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

Nodes == Node
LoopProcesses == SlushLoopProcess
QueryProcesses == SlushQueryProcess

ASSUME NoColor \notin Nodes
ASSUME NoMessage \notin (Nodes \X Nodes)

ColorOf == (x \in Nodes) : IF x = NoColor THEN NoColor ELSE CHOOSE y \in Nodes : y = x

MessageType == {"SlushQuery", "SlushQueryReply", "SlushTermination"}

VARIABLES assignment, messages, loopStep, queryStep, sample, iteration

vars == <<assignment, messages, loopStep, queryStep, sample, iteration>>

Query == [kind : "SlushQuery", to : QueryProcesses, from : LoopProcesses, color : Nodes \cup {NoColor}]
Reply == [kind : "SlushQueryReply", to : LoopProcesses, from : QueryProcesses, color : Nodes \cup {NoColor}]
Terminate == [kind : "SlushTermination", to : LoopProcesses]

QueryMessage == Query
ReplyMessage == Reply
TerminateMessage == Terminate

TypeOK ==
  /\ assignment \in [Nodes -> Nodes \cup {NoColor}]
  /\ messages \subseteq MessageType
  /\ loopStep \in [LoopProcesses -> {"awaitingColor", "sampling", "processing", "done"}]
  /\ queryStep \in [QueryProcesses -> {"replied", "done"}]
  /\ sample \in [LoopProcesses -> SUBSET QueryProcesses]
  /\ iteration \in [LoopProcesses -> 0..SlushIterationCount]

Init ==
  /\ assignment = [x \in Nodes |-> NoColor]
  /\ messages = {}
  /\ loopStep = [p \in LoopProcesses |-> "awaitingColor"]
  /\ queryStep = [q \in QueryProcesses |-> "replied"]
  /\ sample = [p \in LoopProcesses |-> {}]
  /\ iteration = [p \in LoopProcesses |-> 0]

ClientAssignColor(n) ==
  /\ assignment[n] = NoColor
  /\ \E c \in Nodes : assignment' = [assignment EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, loopStep, queryStep, sample, iteration>>

RequireColor(p) ==
  /\ loopStep[p] = "awaitingColor"
  /\ \E n \in Nodes : <<p, n>> \in HostMapping /\ assignment[n] # NoColor
  /\ loopStep' = [loopStep EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<assignment, messages, queryStep, sample, iteration>>

QuerySampleSet(p) ==
  /\ loopStep[p] = "sampling"
  /\ iteration[p] < SlushIterationCount
  /\ sample[p] = {}
  /\ \E S \in SUBSET QueryProcesses :
       /\ Cardinality(S) = SampleSetSize
       /\ sample' = [sample EXCEPT ![p] = S]
  /\ \E n \in Nodes : <<p, n>> \in HostMapping
       /\ \E q \in QueryProcesses : <<p, q>> \in HostMapping /\ n = q
           => messages' = messages \cup {[kind |-> "SlushQuery", to |-> q, from |-> p, color |-> assignment[n]]}
  /\ UNCHANGED <<assignment, loopStep, queryStep, iteration>>

RespondQuery(q) ==
  /\ queryStep[q] = "replied"
  /\ \E m \in messages :
       /\ m.kind = "SlushQuery" /\ m.to = q
       /\ IF assignment[CHOOSE n \in Nodes : <<q, n>> \in HostMapping] = NoColor
          THEN assignment' = [assignment EXCEPT ![CHOOSE n \in Nodes : <<q, n>> \in HostMapping] = m.color]
          ELSE assignment' = assignment
       /\ messages' = (messages \ {m}) \cup {[kind |-> "SlushQueryReply", to |-> m.from, from |-> q, color |-> assignment[CHOOSE n \in Nodes : <<q, n>> \in HostMapping]]}
  /\ queryStep' = [queryStep EXCEPT ![q] = "done"]
  /\ UNCHANGED <<loopStep, sample, iteration>>

TallyReplies(p) ==
  /\ loopStep[p] = "sampling"
  /\ sample[p] # {}
  /\ \A q \in sample[p] : \E m \in messages :
       /\ m.kind = "SlushQueryReply" /\ m.to = p /\ m.from = q
  /\ LET Count(c) == Cardinality({q \in sample[p] : \E m \in messages : m.kind = "SlushQueryReply" /\ m.to = p /\ m.from = q /\ m.color = c}) IN
       LET flipped == (IF \E c \in Nodes : Count(c) >= PickFlipThreshold THEN CHOOSE c \in Nodes : Count(c) >= PickFlipThreshold ELSE NoColor) IN
         assignment' = IF flipped = NoColor THEN assignment ELSE [assignment EXCEPT ![CHOOSE n \in Nodes : <<p, n>> \in HostMapping] = flipped]
  /\ messages' = {m \in messages : ~ (m.kind = "SlushQueryReply" /\ m.to = p /\ m.from \in sample[p])}
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]
  /\ loopStep' = [loopStep EXCEPT ![p] = "processing"]
  /\ UNCHANGED <<queryStep>>

LoopTerminate(p) ==
  /\ loopStep[p] = "processing"
  /\ iteration[p] >= SlushIterationCount
  /\ loopStep' = [loopStep EXCEPT ![p] = "done"]
  /\ messages' = messages \cup {[kind |-> "SlushTermination", to |-> p]}
  /\ UNCHANGED <<assignment, queryStep, sample, iteration>>

QueryLoopExit(q) ==
  /\ queryStep[q] = "done"
  /\ \A p \in LoopProcesses : loopStep[p] = "done"
  /\ queryStep' = [queryStep EXCEPT ![q] = "replied"]
  /\ UNCHANGED <<assignment, messages, loopStep, sample, iteration>>

Next ==
  \/ \E n \in Nodes : ClientAssignColor(n) \/ RequireColor(CHOOSE p \in LoopProcesses : <<p, n>> \in HostMapping)
  \/ \E p \in LoopProcesses : QuerySampleSet(p) \/ TallyReplies(p) \/ LoopTerminate(p)
  \/ \E q \in QueryProcesses : RespondQuery(q) \/ QueryLoopExit(q)

Spec == Init /\ [][Next]_vars

Termination == <>(\A p \in LoopProcesses : loopStep[p] = "done")

====