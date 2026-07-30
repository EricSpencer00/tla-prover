---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* Capacity check made on the constant set itself, not on the run-time
\* message set (which is why the invariant below is not trivial).
CapacityOK ==
  /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
  /\ Cardinality(Node) = Cardinality(SlushQueryProcess)

\* Message tags; the client request is modeled as a client action rather
\* than a message, so NoMessage is only ever used as the empty set.
Query == "query"
Reply == "reply"
Done == "done"

VARIABLES assignment, messages, pc, sample, iters

Color == {"col1", "col2", NoColor}

TypeSet(T) == [kind: T, from: SlushLoopProcess \cup SlushQueryProcess,
                 to: SlushLoopProcess \cup SlushQueryProcess,
                 payload: Color]

Vars == <<assignment, messages, pc, sample, iters>>

TypeOK ==
  /\ assignment \in [Node -> Color]
  /\ messages \subseteq
        TypeSet(Query) \cup TypeSet(Reply) \cup TypeSet(Done)
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} ->
                {"waitAssign", "select", "tally", "done", "reply", "waitDone"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ assignment = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |
            IF p \in SlushLoopProcess THEN "waitAssign" ELSE "reply"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

\* The client tags uncolored nodes with a random color.
ClientAssignColor ==
  \E n \in Node, c \in Color :
    /\ n \notin {p[1] : p \in HostMapping}
    /\ assignment' = [assignment EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sample, iters>>

RequireNodeColor ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "waitAssign"
    /\ \E n \in Node : <<n, p, "loop">> \in HostMapping
    /\ assignment[n] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "select"]
    /\ UNCHANGED <<assignment, messages, sample, iters>>

QuerySampleSet ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "select"
    /\ \E S \in SUBSET SlushQueryProcess :
         /\ Cardinality(S) = SampleSetSize
         /\ \A q \in S : <<p, q, NoColor>> \notin messages
         /\ sample' = [sample EXCEPT ![p] = S]
    /\ messages' = messages \cup
                    {<<Query, p, q, NoColor>> : q \in sample[p]}
    /\ UNCHANGED <<assignment, pc, iters>>

\* Query processes adopt the query color if still uncolored.
RespondToQuery ==
  \E m \in messages :
    /\ m.kind = Query
    /\ messages' = messages \ {m}
    /\ \E n \in Node :
         /\ <<n, m.from, "query">> \in HostMapping
         /\ assignment' = [assignment EXCEPT ![n] =
               IF assignment[n] = NoColor THEN m.payload ELSE assignment[n]]
         /\ messages' = messages \cup
               {<<Reply, m.from, m.to, assignment[n]>>}
    /\ UNCHANGED <<pc, sample, iters>>

TallyReplies ==
  \E p \in SlushLoopProcess :
    /\ pc[p] \in {"select", "tally"}
    /\ Cardinality(sample[p]) = SampleSetSize
    /\ \A q \in sample[p] :
         <<Reply, p, q, NoColor>> \notin messages
    /\ LET counts == [c \in Color |-> Cardinality(
                        {q \in sample[p] : <<Reply, p, q, c>> \in messages})]
         IN
           /\ IF \E c \in Color : counts[c] >= PickFlipThreshold
                THEN assignment' = [assignment EXCEPT ![m[1]] = c]
                ELSE assignment' = assignment
           /\ messages' = {m \in messages : m.from # p}
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ iters' = [iters EXCEPT ![p] = IF iters[p] < SlushIterationCount
                                         THEN iters[p] + 1 ELSE iters[p]]
    /\ pc' = [pc EXCEPT ![p] = "select"]
    /\ UNCHANGED <<assignment>>

LoopTerminate ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "select"
    /\ iters[p] = SlushIterationCount
    /\ sample[p] = {}
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ messages' = messages \cup
                   {<<Done, p, q, NoColor>> : q \in SlushQueryProcess}
    /\ UNCHANGED <<assignment, sample, iters>>

QueryLoopExit ==
  \E q \in SlushQueryProcess :
    /\ pc[q] = "reply"
    /\ \A p \in SlushLoopProcess : <<Done, p, q, NoColor>> \in messages
    /\ pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<assignment, messages, sample, iters>>

Next ==
  \/ ClientAssignColor \/ RequireNodeColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Fairness == \A p \in SlushLoopProcess : SF_vars(RequireNodeColor)
             /\ \A q \in SlushQueryProcess : SF_vars(RespondToQuery)

Spec == Init /\ [][Next]_Vars /\ Fairness

AllDone == \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} :
             pc[p] = "done"

Termination == <>(AllDone /\ UNCHANGED Vars)

====