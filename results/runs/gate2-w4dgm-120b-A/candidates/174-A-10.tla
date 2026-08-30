---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

Message == [kind: {"query", "reply", "term"}, procId: Node, src: Node,
            color: {NoColor} \cup Node]

\* hostOf identifies the node a given process belongs to (each process is
\* paired with its containing node in HostMapping).
hostOf(p) == CHOOSE n \in Node : <<n, p, p>> \in HostMapping

VARIABLES
  color,      \* color[n]: the assigned color (or NoColor) for node n
  messages,   \* in-flight messages
  pc,         \* pc[p]: "waiting", "sampling", "tally", "done"
  sample,     \* sample[p]: the set of nodes p queried this round
  loopsDone   \* loopsDone[p]: iterations p has completed

vars == <<color, messages, pc, sample, loopsDone>>

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \cup Node]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"waiting", "sampling", "tally", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ loopsDone \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess |-> "waiting"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopsDone = [p \in SlushLoopProcess |-> 0]

\* External transaction assigning an initial color to an uncolored node.
AssignColor ==
  /\ \E n \in Node, c \in Node :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sample, loopsDone>>

RequireColor(p) ==
  /\ pc[p] = "waiting"
  /\ color[hostOf(p)] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<color, messages, sample, loopsDone>>

\* The loop process samples a fixed-size subset of other nodes.
QuerySampleSet(p) ==
  /\ pc[p] = "sampling"
  /\ sample[p] = {}
  /\ Cardinality(sample[p]) < SampleSetSize
  /\ \E n \in Node :
       /\ n # hostOf(p)
       /\ n \notin sample[p]
       /\ sample' = [sample EXCEPT ![p] = @ \cup {n}]
       /\ messages' = messages \cup
            {[kind |-> "query", procId |-> p, src |-> n, color |-> color[hostOf(p)]]}
  /\ UNCHANGED <<color, pc, loopsDone>>

RespondToQuery ==
  /\ \E m \in messages :
       /\ m.kind = "query"
       /\ LET nb == m.src IN
            /\ color' = [color EXCEPT ![nb] =
                 IF color[nb] = NoColor THEN m.color ELSE color[nb]]
            /\ messages' = (messages \ {m}) \cup
                 {[kind |-> "reply", procId |-> hostOf(m.procId), src |-> nb,
                   color |-> IF color[nb] = NoColor THEN m.color ELSE color[nb]]}
  /\ UNCHANGED <<pc, sample, loopsDone>>

\* A reply only counts once it is from a node in this round's sample set.
TallyReplies(p) ==
  /\ pc[p] = "tally"
  /\ loopsDone[p] < SlushIterationCount
  /\ \E c \in Node :
       LET replies == {m \in messages : m.kind = "reply" /\ m.procId = p
                           /\ m.src \in sample[p] /\ m.color = c} IN
         /\ Cardinality(replies) >= PickFlipThreshold
         /\ color' = [color EXCEPT ![hostOf(p)] = c]
         /\ sample' = [sample EXCEPT ![p] = {}]
         /\ loopsDone' = [loopsDone EXCEPT ![p] = @ + 1]
         /\ pc' = [pc EXCEPT ![p] = "sampling"]
         /\ messages' = {m \in messages : ~(m.kind = "reply" /\ m.procId = p)}
  /\ UNCHANGED <<>>

LoopTermination(p) ==
  /\ pc[p] = "sampling"
  /\ loopsDone[p] = SlushIterationCount
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ messages' = messages \cup
       {[kind |-> "term", procId |-> p, src |-> hostOf(p), color |-> NoColor]}
  /\ UNCHANGED <<color, sample, loopsDone>>

QueryLoopExit ==
  /\ \A p \in SlushQueryProcess : pc[p] = "done"
  /\ pc' = [p \in SlushLoopProcess |-> IF pc[p] = "done" THEN "done" ELSE pc[p]]
  /\ UNCHANGED <<color, messages, sample, loopsDone>>

Next ==
  \/ AssignColor
  \/ RespondToQuery
  \/ QueryLoopExit
  \/ \E p \in SlushLoopProcess :
       RequireColor(p) \/ QuerySampleSet(p) \/ TallyReplies(p) \/ LoopTermination(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(AssignColor)
  /\ SF_vars(QueryLoopExit)

AllProcessesDone == \A p \in SlushLoopProcess : pc[p] = "done"

Termination == <>(AllProcessesDone)

====