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

\* Message tags for the Slush protocol.
MsgTag == {"slush-query", "slush-reply", "slush-done"}

\* A Slush message carries its tag, source and destination process, and the
\* sender's (loop process's) current color, which is the only payload.
Message == [tag: MsgTag, src: SlushLoopProcess \cup SlushQueryProcess,
            dst: SlushQueryProcess \cup SlushLoopProcess, clr: Node \cup {NoColor}]

VARIABLES
  color, msgs, pc, sample, completed

vars == <<color, msgs, pc, sample, completed>>

Nodes == Node
LoopProcs == SlushLoopProcess
QueryProcs == SlushQueryProcess
AllProcs == LoopProcs \cup QueryProcs

TypeOK ==
  /\ color \in [Nodes -> Nodes \cup {NoColor}]
  /\ msgs \subseteq Message
  /\ pc \in [AllProcs -> {"idle", "loop", "query", "done"}]
  /\ sample \in [LoopProcs -> SUBSET QueryProcs]
  /\ completed \in [LoopProcs -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Nodes |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in AllProcs |-> IF p \in QueryProcs THEN "query" ELSE "idle"]
  /\ sample = [lp \in LoopProcs |-> {}]
  /\ completed = [lp \in LoopProcs |-> 0]

AssignColor ==
  /\ \E n \in Nodes :
       /\ color[n] = NoColor
       /\ \E c \in Nodes : color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sample, completed>>

RequireColor ==
  /\ \E lp \in LoopProcs :
       /\ pc[lp] = "idle"
       /\ \E n \in Nodes :
            /\ [lp |-> lp, proc |-> "slush-loop", node |-> n] \in HostMapping
            /\ color[n] # NoColor
            /\ pc' = [pc EXCEPT ![lp] = "loop"]
  /\ UNCHANGED <<color, msgs, sample, completed>>

\* Each loop process samples a random subset (of fixed size) of query processes.
QuerySampleSet ==
  /\ \E lp \in LoopProcs :
       /\ pc[lp] = "loop"
       /\ completed[lp] < SlushIterationCount
       /\ sample[lp] = {}
       /\ \E Q \in SUBSET QueryProcs :
            /\ Cardinality(Q) = SampleSetSize
            /\ sample' = [sample EXCEPT ![lp] = Q]
            /\ msgs' = msgs \cup {[tag |-> "slush-query",
                                   src |-> lp,
                                   dst |-> q,
                                   clr |-> color[[n \in Nodes |
                                                   [lp |-> lp, proc |-> "slush-loop", node |-> n]
                                                   \in HostMapping]]}
                                   : q \in Q]
  /\ UNCHANGED <<color, pc, completed>>

RespondToQuery ==
  /\ \E q \in QueryProcs :
       /\ \E m \in msgs :
            /\ m.tag = "slush-query" /\ m.dst = q
            /\ \E n \in Nodes :
                 /\ [q |-> q, proc |-> "slush-query", node |-> n] \in HostMapping
                 /\ IF color[n] = NoColor
                    THEN color' = [color EXCEPT ![n] = m.clr]
                    ELSE color' = color
                 /\ msgs' = (msgs \ {m}) \cup
                       {[tag |-> "slush-reply", src |-> q, dst |-> m.src,
                         clr |-> IF color[n] = NoColor THEN m.clr ELSE color[n]]}
  /\ UNCHANGED <<pc, sample, completed>>

TallyReplies ==
  /\ \E lp \in LoopProcs :
       /\ pc[lp] = "loop"
       /\ sample[lp] # {}
       /\ \E replies \in SUBSET msgs :
            /\ \A m \in replies : m.tag = "slush-reply" /\ m.dst = lp
            /\ \E n \in Nodes :
                 /\ [lp |-> lp, proc |-> "slush-loop", node |-> n]
                    \in HostMapping
                 /\ LET yes == Cardinality({m \in replies : m.clr = n})
                    IN IF yes >= PickFlipThreshold
                       THEN color' = [color EXCEPT ![n] = n] ELSE color' = color
            /\ msgs' = msgs \ replies
            /\ sample' = [sample EXCEPT ![lp] = {}]
            /\ completed' = [completed EXCEPT ![lp] = completed[lp] + 1]
  /\ UNCHANGED pc

LoopTermination ==
  /\ \E lp \in LoopProcs :
       /\ pc[lp] = "loop"
       /\ completed[lp] = SlushIterationCount
       /\ pc' = [pc EXCEPT ![lp] = "done"]
       /\ msgs' = msgs \cup
            {[tag |-> "slush-done", src |-> lp, dst |-> lp, clr |-> NoColor]}
  /\ UNCHANGED <<color, sample, completed>>

QueryLoopExit ==
  /\ \A q \in QueryProcs : pc[q] = "query"
  /\ \A m \in msgs : m.tag # "slush-done"
  /\ pc' = [pc EXCEPT ![q] = "done" : q \in QueryProcs]
  /\ UNCHANGED <<color, msgs, sample, completed>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

TypeInvariant == TypeOK

AllDone == \A p \in AllProcs : pc[p] = "done"

Termination == <>(AllDone)
====