---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess,
  HostMapping, SlushIterationCount, SampleSetSize,
  PickFlipThreshold, NoColor, NoMessage

\* Two possible colors for the Slush network to resolve to.
Colors == {"a", "b"}

\* A paired host maps a node to its loop process and its query process.
Hosts == (Node \X SlushLoopProcess \X SlushQueryProcess)

VARIABLES
  color,    \* color[n]: each node's current color, or NoColor.
  message,  \* in-flight messages (queries, replies, terminations).
  pc,       \* pc[p]: each process's current execution step.
  sample,   \* sample[p]: the sampled peers of each loop process.
  iter      \* iter[p]: loop iterations completed per loop process.

vars == <<color, message, pc, sample, iter>>

\* Three message shapes: Query (loop --> query), Reply (query --> loop),
\* and Termination (a loop announcing its final iteration).
Message == [kind: {"Query", "Reply", "Termination"},
            to:  Node \cup SlushLoopProcess \cup SlushQueryProcess,
            col: Colors \cup {NoColor, NoMessage}]

TypeOK ==
  /\ color \in [Node -> Colors \cup {NoColor}]
  /\ message \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"init", "waiting", "voting", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ message = {}
  /\ pc = [p \in (SlushLoopProcess \union SlushQueryProcess \union {"client"}) |-> "init"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iter = [p \in SlushLoopProcess |-> 0]

\* The client assigns a random color to an uncolored node (an external request).
AssignColor ==
  /\ pc["client"] = "init"
  /\ \E n \in Node, c \in Colors :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<message, pc, sample, iter>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "init"
       /\ \E c \in Colors : color[CHOOSE n \in Node : <<n, p, CHOOSE q \in SlushQueryProcess : <<n, p, q>> >> = c]
       /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<color, message, sample, iter>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waiting"
       /\ iter[p] < SlushIterationCount
       /\ \E peers \in SUBSET Node :
            /\ Cardinality(peers) = SampleSetSize
            /\ peers # {CHOOSE n \in Node : <<n, p, CHOOSE q \in SlushQueryProcess : <<n, p, q>> >>}
            /\ message' = message \cup
                 {[kind |-> "Query", to |-> <<n, p, CHOOSE q \in SlushQueryProcess : <<n, p, q>> >>,
                   col |-> color[CHOOSE n \in Node : <<n, p, CHOOSE q \in SlushQueryProcess : <<n, p, q>> >>]] : n \in peers}
            /\ sample' = [sample EXCEPT ![p] = peers]
       /\ pc' = [pc EXCEPT ![p] = "voting"]
  /\ UNCHANGED <<color, iter>>

RespondToQuery ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "init"
       /\ \E m \in message :
            /\ m.kind = "Query" /\ m.to = q
            /\ LET n == CHOOSE n \in Node : <<n, CHOOSE p \in SlushLoopProcess : <<n, p, q>> >> = m.to
               IN color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN m.col ELSE color[n]]
            /\ message' = (message \ {m}) \union
                 {[kind |-> "Reply", to |-> CHOOSE p \in SlushLoopProcess : <<n, p, q>>,
                   col |-> color[CHOOSE n \in Node: <<n, p, q>> = q]]}
       /\ pc' = [pc EXCEPT ![q] = "waiting"]
  /\ UNCHANGED <<sample, iter>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "voting"
       /\ \E msgs \in SUBSET message :
            /\ Cardinality(msgs) = Cardinality(sample[p])
            /\ \A m \in msgs :
                 /\ m.kind = "Reply" /\ m.to = p
                 /\ CHOOSE n \in sample[p] : <<n, p, CHOOSE q \in SlushQueryProcess : <<n, p, q>> >> = m.to
            /\ LET count == [c \in Colors |-> Cardinality({m \in msgs : m.col = c})]
               IN color' = [color EXCEPT ![CHOOSE n \in Node : <<n, p, CHOOSE q \in SlushQueryProcess : <<n, p, q>> >>] =
                               IF \E c \in Colors : count[c] >= PickFlipThreshold THEN
                                   CHOOSE c \in Colors : count[c] >= PickFlipThreshold
                                 ELSE color[CHOOSE n \in Node : <<n, p, CHOOSE q \in SlushQueryProcess : <<n, p, q>> >>]]
            /\ message' = message \ msgs
       /\ pc' = IF iter[p] + 1 = SlushIterationCount
                   THEN [pc EXCEPT ![p] = "done"]
                   ELSE [pc EXCEPT ![p] = "waiting"]
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ iter' = [iter EXCEPT ![p] = iter[p] + 1]

LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "done"
       /\ message' = message \union {[kind |-> "Termination", to |-> p, col |-> NoMessage]}
       /\ pc' = [pc EXCEPT ![p] = "init"]
  /\ UNCHANGED <<color, sample, iter>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "waiting"
       /\ \A p \in SlushLoopProcess : pc[p] = "init"
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, message, sample, iter>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
          /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
          /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
          /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit)

\* Terminates every loop and query process; convergence to a single color is
\* probabilistic and not modeled here.
AllProcessesTerminate ==
  <>(\A p \in (SlushLoopProcess \union SlushQueryProcess): pc[p] = "done")

====