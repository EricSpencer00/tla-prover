---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush is the simplest member of the Snow family of probabilistic
\* consensus protocols.  A node repeatedly samples random peers and adopts
\* a sufficiently popular opinion; the network then converges to one
\* color (metastability).  This PlusCal model is executable pseudocode,
\* not a probabilistic verifier -- it models the control flow and the
\* type-correctness of messages, and it checks termination.

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME SlushLoopProcess \in (Node -> Nat)
ASSUME SlushQueryProcess \in (Node -> Nat)
ASSUME Cardinality(Node) = Cardinality(SlushLoopProcess)
ASSUME Cardinality(Node) = Cardinality(SlushQueryProcess)
ASSUME Cardinality(HostMapping) = Cardinality(Node)

\* colorOf: the Slush opinion held by each node (or uncolored).  inbox:
\* the in-flight messages, carrying per-sample replies and a termination
\* broadcast.  pc: a program counter per process.  sampleSet: the peers
\* currently being queried by each loop process.  iteration: the count of
\* completed sampling rounds per loop process.
VARIABLES colorOf, inbox, pc, sampleSet, iteration

VARIABLES == <<colorOf, inbox, pc, sampleSet, iteration>>

\* A query reply contains the originating process and the responder's
\* current opinion, so the loop process can tally the sample.
Message == [src: SlushLoopProcess, dst: SlushQueryProcess, kind: {"query", "queryReply", "termination"}, opinion: {NoColor} \cup (Node \X {0, 1})]

TypeOK ==
  /\ colorOf \in [Node -> {NoColor} \cup (Node \X {0, 1})]
  /\ inbox \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {0} -> Nat]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> Nat]

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {0} |-> 0]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iteration = [p \in SlushLoopProcess |-> 0]

\* The client process assigns initial colors to uncolored nodes.
AssignColor(n, c) ==
  /\ colorOf[n] = NoColor
  /\ colorOf' = [colorOf EXCEPT ![n] = <<n, c>>]
  /\ UNCHANGED <<inbox, pc, sampleSet, iteration>>

RequireColor(p) ==
  /\ pc[p] = 0
  /\ \E n \in Node : <<n, SlushLoopProcess[n]>> = p /\ colorOf[n] # NoColor
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<colorOf, inbox, sampleSet, iteration>>

\* The loop process samples a fixed-size set of peers to query this round.
QuerySampleSet(p) ==
  /\ pc[p] = 1
  /\ iteration[p] < SlushIterationCount
  /\ \E qs \in SUBSET SlushQueryProcess :
       /\ Cardinality(qs) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![p] = qs]
  /\ inbox' = inbox \cup {[src |-> p, dst |-> q, kind |-> "query", opinion |-> colorOf[CHOOSE n \in Node : SlushLoopProcess[n] = p]] : q \in qs}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<colorOf, iteration>>

\* A query process answers with its node's current opinion; if the node
\* is uncolored it adopts the query's opinion before replying.
RespondQuery(m) ==
  /\ m \in inbox
  /\ m.kind = "query"
  /\ LET q == m.dst, p == m.src, c == m.opinion IN
       /\ \E n \in Node : <<n, q>> \in HostMapping
       /\ LET qOpinion == IF colorOf[CHOOSE n \in Node : <<n, q>> \in HostMapping] = NoColor
                           THEN c
                           ELSE colorOf[CHOOSE n \in Node : <<n, q>> \in HostMapping] IN
          /\ colorOf' = [colorOf EXCEPT ![CHOOSE n \in Node : <<n, q>> \in HostMapping] = qOpinion]
          /\ inbox' = (inbox \ {m}) \cup {[src |-> p, dst |-> q, kind |-> "queryReply", opinion |-> qOpinion]}
  /\ UNCHANGED <<pc, sampleSet, iteration>>

\* The loop process tallies replies and adopts a majority color.
TallyReplies(p) ==
  /\ pc[p] = 2
  /\ \A q \in sampleSet[p] : [src |-> p, dst |-> q, kind |-> "queryReply", opinion |-> NoColor] \notin inbox
  /\ LET r0 == Cardinality({q \in sampleSet[p] : [src |-> p, dst |-> q, kind |-> "queryReply", opinion |-> <<p, 0>>] \in inbox})
         r1 == Cardinality({q \in sampleSet[p] : [src |-> p, dst |-> q, kind |-> "queryReply", opinion |-> <<p, 1>>] \in inbox}) IN
       /\ colorOf' = [colorOf EXCEPT ![CHOOSE n \in Node : SlushLoopProcess[n] = p] = IF r0 >= PickFlipThreshold THEN <<p, 0>> ELSE IF r1 >= PickFlipThreshold THEN <<p, 1>> ELSE colorOf[CHOOSE n \in Node : SlushLoopProcess[n] = p]]
  /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
  /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]
  /\ inbox' = {m \in inbox : m.dst # p}
  /\ pc' = [pc EXCEPT ![p] = 1]

TerminateLoop(p) ==
  /\ iteration[p] >= SlushIterationCount
  /\ pc[p] # 3
  /\ inbox' = inbox \cup {[src |-> p, dst |-> 0, kind |-> "termination", opinion |-> <<0, 0>>]}
  /\ pc' = [pc EXCEPT ![p] = 3]
  /\ UNCHANGED <<colorOf, sampleSet, iteration>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = 3
  /\ \A q \in SlushQueryProcess : pc[q] = 1
  /\ pc' = [pc EXCEPT ![q] = 2 : q \in SlushQueryProcess]
  /\ UNCHANGED <<colorOf, inbox, sampleSet, iteration>>

Next ==
  \/ \E n \in Node, c \in {0, 1} : AssignColor(n, c)
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : QuerySampleSet(p)
  \/ \E m \in inbox : RespondQuery(m)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : TerminateLoop(p)
  \/ QueryLoopExit

Spec == Init /\ [][Next]_Variables /\ WF_Variables(\E m \in inbox : RespondQuery(m))

AllProcessesDone == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] >= 3

TerminationProperty == <>AllProcessesDone

====