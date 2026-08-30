---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

Nodes == Node

QueryProcesses == SlushQueryProcess
LoopProcesses == SlushLoopProcess

MessageType == {"query", "queryreply", "termination"}

\* A query message always carries the sender's current color; a reply names both the
\* inquiring loop process and the responder's color.
Message == [type : MessageType, to : Nodes \cup LoopProcesses, from : Nodes \cup LoopProcesses,
            col : {NoColor} \cup Nodes, sample : SUBSET Nodes]

VARIABLES assign, messages, pc, sample, iters

vars == <<assign, messages, pc, sample, iters>>

TypeOK ==
  /\ assign \in [Nodes -> {NoColor} \cup Nodes]
  /\ messages \subseteq Message
  /\ pc \in [Nodes \cup LoopProcesses -> {"ready", "waiting", "quering", "done"}]
  /\ sample \in [LoopProcesses -> SUBSET Nodes]
  /\ iters \in [LoopProcesses -> 0..SlushIterationCount]

Init ==
  /\ assign = [n \in Nodes |-> NoColor]
  /\ messages = {}
  /\ pc = [x \in Nodes \cup LoopProcesses |-> "ready"]
  /\ sample = [l \in LoopProcesses |-> {}]
  /\ iters = [l \in LoopProcesses |-> 0]

HostOf(x) == CHOOSE n \in Nodes : <<n, x, NoMessage>> \in HostMapping

\* The client assigns an initial color to an uncolored node (a network transaction).
ClientAssign(n) ==
  /\ pc[n] \notin {"waiting", "quering", "done"}
  /\ assign[n] = NoColor
  /\ \E c \in Nodes : assign' = [assign EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sample, iters>>

RequireColor(l) ==
  /\ pc[l] = "ready"
  /\ assign[HostOf(l)] \in Nodes
  /\ pc' = [pc EXCEPT ![l] = "waiting"]
  /\ UNCHANGED <<assign, messages, sample, iters>>

QuerySet(l) ==
  /\ pc[l] = "waiting"
  /\ iters[l] < SlushIterationCount
  /\ \E Q \in SUBSET Nodes :
       /\ Cardinality(Q) = SampleSetSize
       /\ Q # {}
       /\ sample' = [sample EXCEPT ![l] = Q]
       /\ messages' = messages \cup {[type |-> "query", to |-> m, from |-> l,
                                      col |-> assign[HostOf(l)], sample |-> Q] : m \in Q}
  /\ pc' = [pc EXCEPT ![l] = "quering"]
  /\ UNCHANGED <<assign, iters>>

Respond(m) ==
  /\ m.type = "query"
  /\ m \notin messages
  /\ LET a == HostOf(m.from) IN
       /\ assign' = IF assign[a] = NoColor THEN [assign EXCEPT ![a] = m.col] ELSE assign
       /\ messages' = messages \cup {[type |-> "queryreply", to |-> m.from, from |-> a, col |-> assign[a], sample |-> {}]}
  /\ UNCHANGED <<pc, sample, iters>>

\* The loop process waits for every sampled peer to answer before it may flip.
Tally(l) ==
  /\ pc[l] = "quering"
  /\ sample[l] # {}
  /\ \A m \in sample[l] : [type |-> "queryreply", to |-> l, from |-> m, col |-> assign[m], sample |-> {}] \in messages
  /\ LET counts == [n \in Nodes |-> Cardinality({m \in sample[l] : assign[m] = n})] IN
       assign' = IF \E n \in Nodes : counts[n] >= PickFlipThreshold THEN
                    [assign EXCEPT ![HostOf(l)] = CHOOSE n \in Nodes : counts[n] >= PickFlipThreshold]
                 ELSE assign
  /\ sample' = [sample EXCEPT ![l] = {}]
  /\ iters' = [iters EXCEPT ![l] = iters[l] + 1]
  /\ pc' = [pc EXCEPT ![l] = "waiting"]
  /\ UNCHANGED messages

Terminate(l) ==
  /\ pc[l] \in {"waiting", "quering"}
  /\ iters[l] >= SlushIterationCount
  /\ messages' = messages \cup {[type |-> "termination", to |-> NoMessage, from |-> l, col |-> NoColor, sample |-> {}]}
  /\ pc' = [pc EXCEPT ![l] = "done"]
  /\ UNCHANGED <<assign, sample, iters>>

QueryLoopExit ==
  /\ \A q \in QueryProcesses : pc[q] = "ready"
  /\ \A l \in LoopProcesses : pc[l] = "done"
  /\ pc' = [q \in QueryProcesses |-> "done"]
  /\ UNCHANGED <<assign, messages, sample, iters>>

Next ==
  \/ QueryLoopExit
  \/ \E n \in Nodes : ClientAssign(n)
  \/ \E l \in LoopProcesses : RequireColor(l) \/ QuerySet(l) \/ Tally(l) \/ Terminate(l)
  \/ \E m \in messages : Respond(m)

Spec == Init /\ [][Next]_vars /\ WF_vars(QueryLoopExit)
        /\ (\A n \in Nodes : SF_vars(ClientAssign(n)))
        /\ (\A l \in LoopProcesses : SF_vars(RequireColor(l)) /\ WF_vars(QuerySet(l)) /\ SF_vars(Tally(l)))

TypeInvariant == TypeOK

Termination == \A x \in Nodes \cup LoopProcesses : pc[x] = "done"

====