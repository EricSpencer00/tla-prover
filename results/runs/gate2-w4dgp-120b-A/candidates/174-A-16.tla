---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Node is the set of participants. For each node n there is exactly one loop
\* process that drives Slush (n's own peer sampling / voting loop) and exactly
\* one query process that replies to incoming queries. HostMapping ties each loop
\* process and each query process to the node it runs on.
\* SlushIterationCount bounds how many sampling rounds any loop process may take,
\* SampleSetSize is how many peers are sampled per round, and PickFlipThreshold
\* is the minimum number of matching replies needed to adopt a new color.
\* NoColor marks an uncolored node, and NoMessage is the special message value
\* emitted when the client process has no uncolored node to assign.

\* Because TLA+ has no probabilistic primitives, the sampling step below picks
\* an arbitrary sample of the required size; a real implementation would draw it
\* uniformly at random, and the analysis would then appeal to the Chernoff bound
\* to argue that the network converges exponentially quickly with high probability.
\* What the model can prove is purely structural: the type-correctness invariant,
\* and that every process eventually reaches a done state.

VARIABLES colorOf, messages, pc, sample, iteration

vars == <<colorOf, messages, pc, sample, iteration>>

Range(s) == {s[k] : k \in DOMAIN s}
HostOfLoop(p) == (CHOOSE t \in HostMapping : t[2] = p)[1]
HostOfQuery(p) == (CHOOSE t \in HostMapping : t[3] = p)[1]

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "init"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iteration = [p \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  /\ pc["client"] = "init"
  /\ NoColor \in Range(colorOf)
  /\ \E n \in Node :
       /\ colorOf[n] = NoColor
       /\ \E c \in {0, 1} : colorOf' = [colorOf EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "assigned"]
  /\ UNCHANGED <<messages, sample, iteration>>

ClientIdle ==
  /\ pc["client"] = "assigned"
  /\ NoColor \notin Range(colorOf)
  /\ pc' = [pc EXCEPT !["client"] = "done"]
  /\ UNCHANGED <<colorOf, messages, sample, iteration>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "init"
       /\ colorOf[HostOfLoop(p)] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<colorOf, messages, sample, iteration>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "sampling"
       /\ iteration[p] < SlushIterationCount
       /\ LET candidates == Node \ {HostOfLoop(p)}
              sampleSet == CHOOSE s \in SUBSET candidates :
                             Cardinality(s) = SampleSetSize
                           /\ \A n \in s :
                                \E q \in SlushQueryProcess :
                                  HostOfQuery(q) = n
                                 /\ ~ \E m \in messages : m[1] = q /\ m[2] = "query"
                                 /\ messages' = messages \cup
                                      {[1 |-> q, 2 |-> "query", 3 |-> colorOf[HostOfLoop(p)]]}
               /\ sample' = [sample EXCEPT ![p] = sampleSet]
               /\ pc' = [pc EXCEPT ![p] = "waiting"]
     IN UNCHANGED <<colorOf, iteration>>

RespondToQuery ==
  /\ \E m \in messages :
       /\ m[2] = "query"
       /\ LET host == HostOfQuery(m[1])
              replyColor == IF colorOf[host] = NoColor THEN m[3] ELSE colorOf[host]
              replyMsg == [1 |-> m[1], 2 |-> "reply", 3 |-> replyColor]
          IN colorOf' = [colorOf EXCEPT ![host] = replyColor]
             /\ messages' = (messages \ {m}) \cup {replyMsg}
  /\ UNCHANGED <<pc, sample, iteration>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waiting"
       /\ \A n \in sample[p] : HostOfQuery(n) \in Range([m \in messages : m[1] = n /\ m[2] = "reply"])
       /\ LET replies == [m \in messages : m[1] \in sample[p] /\ m[2] = "reply"]
              count(c) == Cardinality({m \in replies : m[3] = c})
              best == IF count(0) > count(1) THEN 0 ELSE 1
          IN colorOf' = [colorOf EXCEPT ![HostOfLoop(p)] = best]
             /\ sample' = [sample EXCEPT ![p] = {}]
             /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]
             /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED messages

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "sampling"
       /\ iteration[p] = SlushIterationCount
       /\ messages' = messages \cup {[1 |-> p, 2 |-> "term", 3 |-> NoMessage]}
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<colorOf, sample, iteration>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "init"
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<colorOf, messages, sample, iteration>>

Next ==
  \/ ClientAssignColor \/ ClientIdle \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
         /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)

TypeInvariant ==
  /\ colorOf \in [Node -> {NoColor, 0, 1}]
  /\ messages \subseteq [1..3 -> {NoMessage, "query", "reply", "term"}]

ProcessTermination == <>(\A p \in (SlushLoopProcess \cup SlushQueryProcess) : pc[p] = "done")

====