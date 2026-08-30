---- MODULE Slush ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Types: Color is a node-coordinated assignment (two colors or uncolored);
\* Message encodes all three message kinds in one finite type.
Color == {0, 1, NoColor}

Message == [kind: {"query", "queryReply", "termination"} |
              src: SlushLoopProcess \cup SlushQueryProcess,
              dst: SlushLoopProcess \cup SlushQueryProcess,
              col: Color]

\* Pairing: which loop/query process sits on which node.
LoopHost(x) == CHOOSE n \in Node : <<n, x, NoMessage>> \in HostMapping
QueryHost(x) == CHOOSE n \in Node : <<n, NoMessage, x>> \in HostMapping

\* A loop process may only sample peers, never itself, so LeaveMe excludes its own host.
LeaveMe(S, x) == S \ {QueryHost(x)}

VARIABLES assignment, messages, pc, sample, iteration

vars == <<assignment, messages, pc, sample, iteration>>

TypeInvariant ==
  /\ assignment \in [Node -> Color]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"waiting", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> 0 .. SlushIterationCount]

Init ==
  /\ assignment = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [x \in SlushLoopProcess |-> "waiting"]
  /\ sample = [x \in SlushLoopProcess |-> {}]
  /\ iteration = [x \in SlushLoopProcess |-> 0]

\* Client requests assign the first colors, one uncolored node at a time.
ClientAssignColor ==
  /\ \E n \in Node, col \in {0, 1} :
       /\ assignment[n] = NoColor
       /\ assignment' = [assignment EXCEPT ![n] = col]
  /\ UNCHANGED <<messages, pc, sample, iteration>>

RequireColor ==
  /\ \E x \in SlushLoopProcess :
       /\ pc[x] = "waiting"
       /\ assignment[LoopHost(x)] # NoColor
       /\ pc' = [pc EXCEPT ![x] = "sampling"]
  /\ UNCHANGED <<assignment, messages, sample, iteration>>

QuerySampleSet ==
  /\ \E x \in SlushLoopProcess :
       /\ pc[x] = "sampling"
       /\ iteration[x] < SlushIterationCount
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Cardinality(Q) = SampleSetSize
            /\ Q = LeaveMe(Q, x)
            /\ sample' = [sample EXCEPT ![x] = Q]
            /\ messages' = messages \cup
                 {[kind |-> "query", src |-> x, dst |-> q, col |-> assignment[LoopHost(x)]] : q \in Q}
  /\ UNCHANGED <<assignment, pc, iteration>>

RespondToQuery ==
  /\ \E m \in messages :
       /\ m.kind = "query"
       /\ LET col == IF assignment[QueryHost(m.dst)] = NoColor
                    THEN m.col ELSE assignment[QueryHost(m.dst)] IN
            assignment' = [assignment EXCEPT ![QueryHost(m.dst)] = col]
       /\ messages' = (messages \ {m}) \cup
            {[kind |-> "queryReply", src |-> m.dst, dst |-> m.src, col |-> col]}
  /\ UNCHANGED <<pc, sample, iteration>>

TallyReplies ==
  /\ \E x \in SlushLoopProcess :
       /\ pc[x] = "sampling"
       /\ sample[x] # {}
       /\ \A q \in sample[x] : [kind |-> "queryReply", src |-> q, dst |-> x, col |-> NoColor] \in messages
       /\ LET tallies == [col \in {0, 1} |-> Cardinality({q \in sample[x] :
            [kind |-> "queryReply", src |-> q, dst |-> x, col |-> col] \in messages})] IN
            assignment' = [assignment EXCEPT ![LoopHost(x)] =
                             IF tallies[0] >= PickFlipThreshold THEN 0
                             ELSE IF tallies[1] >= PickFlipThreshold THEN 1
                             ELSE assignment[LoopHost(x)]]
       /\ messages' = messages \ {[kind |-> "queryReply", src |-> q, dst |-> x, col |-> NoColor] : q \in sample[x]}
       /\ sample' = [sample EXCEPT ![x] = {}]
       /\ pc' = [pc EXCEPT ![x] = "tallying"]
  /\ UNCHANGED <<iteration>>

LoopTermination ==
  /\ \E x \in SlushLoopProcess :
       /\ pc[x] = "tallying"
       /\ iteration[x] + 1 >= SlushIterationCount
       /\ pc' = [pc EXCEPT ![x] = "done"]
       /\ messages' = messages \cup
            {[kind |-> "termination", src |-> x, dst |-> NoMessage, col |-> NoColor]}
  /\ iteration' = [iteration EXCEPT ![x] = iteration[x] + 1]
  /\ UNCHANGED <<assignment, sample>>

QueryLoopExit ==
  /\ \E x \in SlushQueryProcess :
       /\ [kind |-> "termination", src |-> NoMessage, dst |-> x, col |-> NoColor] \in messages
       /\ messages' = messages \ {[kind |-> "termination", src |-> NoMessage, dst |-> x, col |-> NoColor]}
  /\ UNCHANGED <<assignment, pc, sample, iteration>>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
        /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

Termination == <>(\A x \in SlushLoopProcess \cup SlushQueryProcess : pc[x] = "done")

====