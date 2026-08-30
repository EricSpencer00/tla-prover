---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount,
  SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Slush loop processes run the main iteration; query processes reply to sample
\* queries. hostOf[g] = n means g is the loop or query process running on node n.
\* The system starts fully uncolored with an empty message set.

NoNode == "noNode"

VARIABLES color, msgs, pc, sampleSet, loopsCompleted, quorum
vars == <<color, msgs, pc, sampleSet, loopsCompleted, quorum>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup SlushLoopProcess]
  /\ msgs \subseteq [type: {NoMessage} \cup {"query", "reply", "done"},
                     src: Node \cup {NoNode}, dst: Node \cup {NoNode},
                     clr: {NoColor} \cup SlushLoopProcess]
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "waiting",
                                                        "active", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ loopsCompleted \in [SlushLoopProcess -> 0..SlushIterationCount]
  /\ quorum \in [SlushLoopProcess -> 0..Cardinality(Node)]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [g \in SlushLoopProcess \cup SlushQueryProcess |-> "idle"]
  /\ sampleSet = [g \in SlushLoopProcess |-> {}]
  /\ loopsCompleted = [g \in SlushLoopProcess |-> 0]
  /\ quorum = [g \in SlushLoopProcess |-> 0]

HostOf(g) == CHOOSE n \in Node : <<g, n>> \in HostMapping

\* A client transaction assigns an initial random color to an uncolored node.
AssignColor(n, c) ==
  /\ color[n] = NoColor
  /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sampleSet, loopsCompleted, quorum>>

\* Loop processes wait for their host node's first color assignment.
RequireHostColor(g) ==
  /\ pc[g] = "idle"
  /\ color[HostOf(g)] # NoColor
  /\ pc' = [pc EXCEPT ![g] = "waiting"]
  /\ UNCHANGED <<color, msgs, sampleSet, loopsCompleted, quorum>>

\* Begin a round by sampling a fixed number of peers and sending queries.
QuerySampleSet(g) ==
  /\ pc[g] = "waiting"
  /\ loopsCompleted[g] < SlushIterationCount
  /\ sampleSet' = [sampleSet EXCEPT ![g] =
        {n \in Node : n # HostOf(g)} \cap (Cardinality({n \in Node : n # HostOf(g)}) > SampleSetSize
                                          ? (CHOOSE S \in SUBSET {n \in Node : n # HostOf(g)} :
                                                Cardinality(S) = SampleSetSize)
                                          : {n \in Node : n # HostOf(g)})
  /\ msgs' = msgs \cup {[type |-> "query", src |-> HostOf(g),
                         dst |-> n, clr |-> color[HostOf(g)]] :
                         n \in sampleSet[g]}
  /\ pc' = [pc EXCEPT ![g] = "active"]
  /\ UNCHANGED <<color, loopsCompleted, quorum>>

\* A query process adopts the query's color if uncolored, then replies.
RespondToQuery(m) ==
  /\ m.type = "query"
  /\ m \in msgs
  /\ msgs' = (msgs \ {m}) \cup {[type |-> "reply", src |-> m.dst, dst |-> m.src,
                                clr |-> IF color[m.dst] = NoColor THEN m.clr ELSE color[m.dst]]}
  /\ color' = [color EXCEPT ![m.dst] = IF color[m.dst] = NoColor THEN m.clr ELSE color[m.dst]]
  /\ UNCHANGED <<pc, sampleSet, loopsCompleted, quorum>>

\* Tally replies; adopt a color once it reaches the flip threshold.
TallyReplies(g) ==
  /\ pc[g] = "active"
  /\ \A n \in sampleSet[g] : \E m \in msgs :
        /\ m.type = "reply"
        /\ m.src = n
        /\ m.dst = HostOf(g)
  /\ quorum' = [quorum EXCEPT ![g] = Cardinality({n \in sampleSet[g] :
                         \E m \in msgs : m.type = "reply" /\ m.src = n /\ m.clr = "red"})]
  /\ color' = [n \in Node |-> IF n = HostOf(g) /\ quorum[g] >= PickFlipThreshold
                              THEN "red" ELSE color[n]]
  /\ sampleSet' = [sampleSet EXCEPT ![g] = {}]
  /\ loopsCompleted' = [loopsCompleted EXCEPT ![g] = loopsCompleted[g] + 1]
  /\ pc' = [pc EXCEPT ![g] = "waiting"]
  /\ UNCHANGED msgs

LoopTermination(g) ==
  /\ pc[g] = "waiting"
  /\ loopsCompleted[g] = SlushIterationCount
  /\ pc' = [pc EXCEPT ![g] = "done"]
  /\ msgs' = msgs \cup {[type |-> "done", src |-> HostOf(g), dst |-> NoNode, clr |-> NoColor]}
  /\ UNCHANGED <<color, sampleSet, loopsCompleted, quorum>>

ExitQueryLoop ==
  /\ \A g \in SlushLoopProcess : pc[g] = "done"
  /\ \A q \in SlushQueryProcess : pc[q] = "idle"
  /\ \A q \in SlushQueryProcess : pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, msgs, sampleSet, loopsCompleted, quorum>>

Next ==
  \/ \E n \in Node, c \in SlushLoopProcess : AssignColor(n, c)
  \/ \E g \in SlushLoopProcess : RequireHostColor(g)
  \/ \E g \in SlushLoopProcess : QuerySampleSet(g)
  \/ \E m \in msgs : RespondToQuery(m)
  \/ \E g \in SlushLoopProcess : TallyReplies(g)
  \/ \E g \in SlushLoopProcess : LoopTermination(g)
  \/ ExitQueryLoop

Spec == Init /\ [][Next]_vars
        /\ \A m \in msgs : WF_vars(RespondToQuery(m))

TypeInvariant == TypeOK

\* Terminates in every reachable run (every process eventually reaches "done").
Termination == <>(\A g \in SlushLoopProcess \cup SlushQueryProcess : pc[g] = "done")
====