---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush is the simplest member of the Snow family of probabilistic consensus
\* protocols. Because TLA+ has no probabilistic primitives, this spec serves
\* mainly as executable pseudocode: it records the message-passing steps
\* exactly as they happen and checks only structural properties (type safety,
\* eventual termination of all processes), never that a single color actually
\* wins -- that latter outcome is truly probabilistic and not TLA+ verifiable.
\* The loop processes sample a random subset of peer nodes each iteration,
\* query their colors, and adopt any color that reaches the flip threshold
\* among replies -- the essence of "metastable" convergence in Snow.

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
           SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Hosts are the two kinds of processes a node runs: the loop that drives
\* Slush's rounds, and the query process that answers peer polls.
Hosts == HostMapping

Pair(p, n) == <<p, n>>

Variable color, messages, pc, sample, iteration

vars == <<color, messages, pc, sample, iteration>>

TypeOK ==
  /\ color \in [Node -> (1..2) \cup {NoColor}]
  /\ messages \subseteq (SlushLoopProcess \cup {NoMessage}) \X (SlushQueryProcess \cup {NoMessage})
       \X (1..2 \cup {NoMessage})
  /\ pc \in [Hosts -> {"waiting", "looping", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [h \in Hosts |-> IF h[2] = "query" THEN "looping" ELSE "waiting"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iteration = [p \in SlushLoopProcess |-> 0]

\* A client assigns an initial color to some uncolored node -- this is the
\* only way a node's color can ever become non-empty, and it is nondeterministic.
AssignColor ==
  /\ \E n \in Node, c \in 1..2 :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sample, iteration>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[Pair(p, "loop")] = "waiting"
       /\ color[Pair(p, "loop")[1]] # NoColor
       /\ pc' = [pc EXCEPT ![Pair(p, "loop")] = "looping"]
  /\ UNCHANGED <<color, messages, sample, iteration>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[Pair(p, "loop")] = "looping"
       /\ iteration[p] < SlushIterationCount
       /\ sample[p] = {}
       /\ \E Q \in SUBSET (Node \ {Pair(p, "loop")[1]}) :
            /\ Cardinality(Q) = SampleSetSize
            /\ sample' = [sample EXCEPT ![p] = Q]
            /\ messages' = messages \cup {Pair(p, Pair(q, "query")) \X {color[Pair(p, "loop")[1]]}
                             : q \in Q}
  /\ UNCHANGED <<color, pc, iteration>>

RespondToQuery ==
  /\ \E m \in messages :
       /\ m[1] # NoMessage /\ m[1] \in SlushLoopProcess /\ m[2] \in SlushQueryProcess /\ m[3] # NoMessage
       /\ \/ \E c \in 1..2 : color' = [color EXCEPT ![Pair(m[2], "query")[1]] = c]
          \/ messages' = (messages \ {m}) \cup
                         {Pair(m[1], Pair(m[2], "query")) \X {color[Pair(m[2], "query")[1]]}}
  /\ UNCHANGED <<pc, sample, iteration>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[Pair(p, "loop")] = "looping"
       /\ sample[p] # {}
       /\ \A q \in sample[p] : Pair(p, Pair(q, "query")) \in messages
       /\ LET tallies == [c \in 1..2 |-> Cardinality({q \in sample[p] : color[q] = c})] IN
            /\ \E c \in 1..2 :
                 /\ tallies[c] >= PickFlipThreshold
                 /\ color' = [color EXCEPT ![Pair(p, "loop")[1]] = c]
            /\ \/ iteration[p] = SlushIterationCount
                 /\ pc' = [pc EXCEPT ![Pair(p, "loop")] = "done"]
                 /\ messages' = messages \cup {Pair(p, NoMessage) \X {NoMessage}}
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]

LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[Pair(p, "loop")] = "done"
       /\ Pair(p, NoMessage) \notin messages
       /\ messages' = messages \cup {Pair(p, NoMessage) \X {NoMessage}}
  /\ UNCHANGED <<color, pc, sample, iteration>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : Pair(p, NoMessage) \in messages
  /\ \A h \in SlushQueryProcess : pc[h] = "looping"
  /\ pc' = [h \in Hosts |-> IF h[2] = "query" THEN "done" ELSE pc[h]]
  /\ UNCHANGED <<color, messages, sample, iteration>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(LoopTerminate)
        /\ WF_vars(TallyReplies)
        /\ WF_vars(LoopTerminate)

TypeInvariant == TypeOK

Termination == <>(\A h \in Hosts : pc[h] = "done")

====