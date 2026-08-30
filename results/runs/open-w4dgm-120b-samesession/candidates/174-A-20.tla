---- MODULE Slush ----
EXTENDS Naturals, Sequences

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* hostOf[n] gives the loop and query process belonging to node n (fixed by HostMapping)
HostOf == [n \in Node |-> CHOOSE p \in HostMapping : p[1] = n]

VARIABLES color, envelope, pc, sample, iteration

vars == <<color, envelope, pc, sample, iteration>>

NodeCount == Cardinality(Node)
QueryCount == Cardinality({ p[2] : p \in HostMapping })
MessageCount == Cardinality(envelope)

\* A message is a query, a query reply (with a color), or a loop termination notice
MessageType == [kind: {"query", "reply", "done"}, proc: SlushLoopProcess \cup SlushQueryProcess,
                 dest: SlushLoopProcess \cup SlushQueryProcess, col: {NoColor} \cup 0..2]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ envelope = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "idle"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iteration = [p \in SlushLoopProcess |-> 0]

RequestsPending == Cardinality({ m \in envelope : m.kind = "query" })
RepliesPending == Cardinality({ m \in envelope : m.kind = "reply" })
DoneCount == Cardinality({ p \in SlushLoopProcess : pc[p] = "done" })

\* The client assigns an initial color to an uncolored node (one of two colors)
AssignColor(n, c) ==
  /\ pc[HostOf[n][2]] = "idle"
  /\ color[n] = NoColor
  /\ color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT ![HostOf[n][2]] = "ready"]
  /\ UNCHANGED <<envelope, sample, iteration>>

\* A loop process waits for its host node to be assigned a color before running
RequireColor(p) ==
  /\ pc[p] = "idle"
  /\ color[HostOf[p][1]] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "ready"]
  /\ UNCHANGED <<color, envelope, sample, iteration>>

\* The loop process samples a fixed peer set and sends a query to each
QueryPeers(p) ==
  /\ pc[p] = "ready"
  /\ iteration[p] < SlushIterationCount
  /\ sample[p] = {}
  /\ \E subset \in (HostMapping \ {HostOf[HostOf[p][1]]}) : Cardinality(subset) = SampleSetSize
       /\ sample' = [sample EXCEPT ![p] = { r[2] : r \in subset }]
       /\ envelope' = envelope \cup
            { [kind |-> "query", proc |-> p, dest |-> r[2], col |-> color[HostOf[p][1]]] : r \in subset }
  /\ pc' = [pc EXCEPT ![p] = "awaiting"]
  /\ UNCHANGED <<color, iteration>>

\* A query process adopts the query color if uncolored, then replies with its color
RespondToQuery(m) ==
  /\ m.kind = "query"
  /\ pc[m.dest] \in {"idle", "ready"}
  /\ color' = [color EXCEPT ![HostOf[m.dest][1]] =
                 IF color[HostOf[m.dest][1]] = NoColor THEN m.col ELSE color[HostOf[m.dest][1]]]
  /\ envelope' = (envelope \ {m}) \cup
       { [kind |-> "reply", proc |-> m.dest, dest |-> m.proc, col |-> color[HostOf[m.dest][1]]] }
  /\ pc' = [pc EXCEPT ![m.dest] = "replying"]
  /\ UNCHANGED <<sample, iteration>>

\* The loop process tallies replies and adopts a color that reaches the flip threshold
TallyReplies(p) ==
  /\ pc[p] = "awaiting"
  /\ \A q \in sample[p] : [kind |-> "reply", proc |-> q, dest |-> p, col |-> NoColor] \notin envelope
  /\ Cardinality({ m \in envelope : m.kind = "reply" /\ m.dest = p /\ m.col = 0 }) >= PickFlipThreshold
       => color' = [color EXCEPT ![HostOf[p][1]] = 0]
  /\ Cardinality({ m \in envelope : m.kind = "reply" /\ m.dest = p /\ m.col = 1 }) >= PickFlipThreshold
       => color' = [color EXCEPT ![HostOf[p][1]] = 1]
  /\ envelope' = { m \in envelope : ~(m.kind = "reply" /\ m.dest = p) }
  /\ pc' = [pc EXCEPT ![p] = "ready"]
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iteration' = [iteration EXCEPT ![p] = @ + 1]

\* After completing its iterations, the loop process broadcasts termination
TerminateLoop(p) ==
  /\ pc[p] = "ready"
  /\ iteration[p] = SlushIterationCount
  /\ envelope' = envelope \cup { [kind |-> "done", proc |-> p, dest |-> NoMessage, col |-> NoMessage] }
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<color, sample, iteration>>

\* Replying processes exit once every loop process has terminated
QueryLoopExit(q) ==
  /\ pc[q] = "replying"
  /\ DoneCount = SlushLoopProcess
  /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, envelope, sample, iteration>>

Next ==
  \/ \E n \in Node, c \in 0..1 : AssignColor(n, c)
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : QueryPeers(p)
  \/ \E m \in envelope : RespondToQuery(m)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : TerminateLoop(p)
  \/ \E q \in SlushQueryProcess : QueryLoopExit(q)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E m \in envelope : RespondToQuery(m))
        /\ WF_vars(\E p \in SlushLoopProcess : TallyReplies(p))

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \cup 0..2]
  /\ envelope \subseteq MessageType
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "ready", "awaiting", "replying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Termination ==
  \A p \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[p] = "done")

====