---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

\* State: each node's color; the in-flight messages; each process's PC; each
\* loop process's sampled peer set; each loop process's completed iteration
\* count.
VARIABLES
  color,
  msgs,
  pc,
  sample,
  iters

vars == <<color, msgs, pc, sample, iters>>

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \cup SlushLoopProcess]
  /\ msgs \subseteq SlushQueryProcess \cup SlushLoopProcess \cup {NoMessage}
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {ClientRequest} -> 0..6]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

HostLoop(n) == CHOOSE p \in SlushLoopProcess :
                 \E t \in HostMapping : t[1] = n /\ t[2] = p
HostQuery(n) == CHOOSE q \in SlushQueryProcess :
                  \E t \in HostMapping : t[1] = n /\ t[3] = q

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {ClientRequest} |-> 0]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

\* Client assigns an initial color to an uncolored node (a new transaction).
AssignColor ==
  /\ \E n \in Node : /\ color[n] = NoColor
                        /\ \E col \in SlushLoopProcess : color' = [color EXCEPT ![n] = col]
  /\ pc' = [pc EXCEPT ![ClientRequest] = 1]
  /\ UNCHANGED <<msgs, sample, iters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 0
       /\ color[HostMapping[\E t \in HostMapping : t[2] = p][1]] # NoColor
       /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<color, msgs, sample, iters>>

\* The loop process samples a random set of peers and queries their colors.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ iters[p] < SlushIterationCount
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Q # {}
            /\ Cardinality(Q) <= SampleSetSize
            /\ sample' = [sample EXCEPT ![p] = Q]
            /\ msgs' = msgs \cup {q : q \in Q}
       /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<color, iters>>

\* A query process answers, adopting the query color if still uncolored.
RespondToQuery ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = 0
       /\ q \in msgs
       /\ LET n == HostMapping[\E t \in HostMapping : t[3] = q][1] IN
          /\ color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN color[HostMapping[\E t \in HostMapping : t[3] = q][1]] ELSE color[n]]
          /\ msgs' = (msgs \ {q}) \cup {HostLoop(n)}
       /\ pc' = [pc EXCEPT ![q] = 1]
  /\ UNCHANGED <<sample, iters>>

\* Once all queried peers have replied, the loop process flips its node's
\* color if one color dominates the sampled replies by the threshold.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 2
       /\ \A q \in sample[p] : HostLoop(q) \in msgs
       /\ LET n == HostMapping[\E t \in HostMapping : t[2] = p][1] IN
            LET tallies ==
                 [col \in SlushLoopProcess |-> Cardinality({q \in sample[p] : color[HostMapping[\E t \in HostMapping : t[3] = q][1]] = col})]
            IN color' = [color EXCEPT ![n] = IF \E col \in SlushLoopProcess : tallies[col] >= PickFlipThreshold THEN CHOOSE col \in SlushLoopProcess : tallies[col] >= PickFlipThreshold ELSE color[n]]
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
       /\ msgs' = (msgs \ {HostLoop(q) : q \in sample[p]}) \cup {p}
       /\ pc' = [pc EXCEPT ![p] = 3]
  /\ UNCHANGED <<color, iters>>

\* After completing, the loop process broadcasts termination.
LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 3
       /\ iters[p] = SlushIterationCount
       /\ pc' = [pc EXCEPT ![p] = 5]
       /\ msgs' = msgs \cup {p}
  /\ UNCHANGED <<color, sample, iters>>

\* With every loop process terminated, query processes exit.
QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = 1
       /\ \A p \in SlushLoopProcess : p \in msgs
       /\ pc' = [pc EXCEPT ![q] = 6]
  /\ UNCHANGED <<color, msgs, sample, iters>>

Quiescent == /\ \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = 5 \/ pc[p] = 6
              /\ \A n \in Node : color[n] # NoColor

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryLoopExit \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(AssignColor) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)
        /\ WF_vars(QueryLoopExit) /\ WF_vars(Quiescent)

Termination == <>(Quiescent /\ UNCHANGED vars)

====