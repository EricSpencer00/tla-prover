---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A SlushLoopProcess is the active part of a node: it samples peers and
\* decides whether to flip the node's color. A SlushQueryProcess simply
\* answers a query from some peer's loop.
SlushProcess == SlushLoopProcess \cup SlushQueryProcess

\* A loop process is done once it has exhausted its iteration budget;
\* a query process is done once every loop has terminated.
ProcessDone(p) == IF p \in SlushLoopProcess THEN loopIter[p] >= SlushIterationCount ELSE terminated

\* Message tags: a loop queries a peer's query process, which replies with its
\* color (or adopts the query's if it is uncolored); a loop also broadcasts
\* termination once it has finished all iterations.
MessageTag == {NoMessage, "query", "queryreply", "terminated"}

VARIABLES
  color,      \* color[n]: Slush color of node n, or NoColor (uncolored)
  message,    \* the set of in-flight messages; each message is a record
  pc,         \* pc[p]: program counter of process p
  sample,     \* sample[p]: the fixed-size set of peers loop p sampled this round
  loopIter    \* loopIter[p]: number of iterations loop p has completed

vars == <<color, message, pc, sample, loopIter>>

\* Each loop process hosts exactly one query process; that coupling is the
\* whole of the network, because a loop queries its peers' query processes.
QueryProc(n) == CHOOSE q \in SlushQueryProcess : <<n, q>> \in HostMapping
LoopProc(n)  == CHOOSE l \in SlushLoopProcess : <<n, l>> \in HostMapping

\* Slush fast-converges but is not deterministic, so the model keeps the
\* sample size fixed and the flip threshold above a single vote.
\* The sample is drawn without replacement: the loop sends one query per
\* selected peer and waits for exactly those replies.
QuorumReached(c) ==
  \E a \in 0..Cardinality(sample[LoopProc(c)]):
    /\ 2 * a >= Cardinality(sample[LoopProc(c)])
    /\ 2 * a >= PickFlipThreshold

TypeOK ==
  /\ color \in [Node -> (0..1) \cup {NoColor}]
  /\ message \subseteq [tag: MessageTag, to: SlushProcess, from: SlushProcess,
                        col: (0..1) \cup {NoColor}]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ message = {}
  /\ pc = [p \in SlushProcess |-> "ready"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopIter = [l \in SlushLoopProcess |-> 0]

\* The client must seed every node before any loop can meaningfully sample.
AssignColor ==
  /\ \E n \in Node, col \in 0..1:
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = col]
  /\ UNCHANGED <<message, pc, sample, loopIter>>

RequireColor ==
  /\ \E l \in SlushLoopProcess:
       /\ pc[l] = "ready"
       /\ color[LoopProc(l)] # NoColor
       /\ pc' = [pc EXCEPT ![l] = "waiting"]
  /\ UNCHANGED <<color, message, sample, loopIter>>

SendQuery ==
  /\ \E l \in SlushLoopProcess:
       /\ pc[l] = "waiting"
       /\ Cardinality(sample[l]) < SampleSetSize
       /\ \E n \in Node:
            /\ <<n, QueryProc(n)>> \notin HostMapping
            /\ <<n, QueryProc(n)>> \notin message
            /\ n # LoopProc(l)
            /\ <<n, QueryProc(n)>> \notin sample[l]
            /\ sample' = [sample EXCEPT ![l] = @ \cup {<<n, QueryProc(n)>>}]
            /\ message' = message \cup {[tag |-> "query", to |-> QueryProc(n),
                                         from |-> l, col |-> color[LoopProc(l)]]}
  /\ UNCHANGED <<color, pc, loopIter>>

ReplyAndAdopt ==
  /\ \E m \in message:
       /\ m.tag = "query"
       /\ color[LoopProc(m.to)] = NoColor
       /\ color' = [color EXCEPT ![LoopProc(m.to)] = m.col]
       /\ message' = (message \ {m}) \cup {[tag |-> "queryreply", to |-> m.from,
                                            from |-> m.to, col |-> m.col]}
  /\ UNCHANGED <<pc, sample, loopIter>>

TallyReplies ==
  /\ \E l \in SlushLoopProcess:
       /\ pc[l] = "waiting"
       /\ Cardinality(sample[l]) = SampleSetSize
       /\ \A r \in sample[l]: \E m \in message: m.tag = "queryreply" /\ m.to = l /\ m.from = r
       /\ QuorumReached(l)
       /\ color' = [color EXCEPT ![LoopProc(l)] = color[LoopProc(l)]]
       /\ message' = message \ {[tag |-> "queryreply", to |-> l, from |-> r, col |-> col[LoopProc(r)]] : r \in sample[l]}
       /\ sample' = [sample EXCEPT ![l] = {}]
       /\ loopIter' = [loopIter EXCEPT ![l] = @ + 1]
       /\ pc' = [pc EXCEPT ![l] = IF loopIter[l] + 1 < SlushIterationCount THEN "waiting" ELSE "done"]
  /\ UNCHANGED <<>>

TerminateLoop ==
  /\ \E l \in SlushLoopProcess:
       /\ pc[l] = "done"
       /\ pc' = [pc EXCEPT ![l] = "terminating"]
       /\ message' = message \cup {[tag |-> "terminated", to |-> NoMessage, from |-> l,
                                    col |-> NoColor]}
  /\ UNCHANGED <<color, sample, loopIter>>

ExitQueryLoop ==
  /\ \E q \in SlushQueryProcess:
       /\ pc[q] = "ready"
       /\ \A l \in SlushLoopProcess: \E m \in message: m.tag = "terminated" /\ m.from = l
       /\ pc' = [pc EXCEPT ![q] = "terminating"]
  /\ UNCHANGED <<color, message, sample, loopIter>>

Next ==
  \/ AssignColor \/ RequireColor \/ SendQuery \/ ReplyAndAdopt
  \/ TallyReplies \/ TerminateLoop \/ ExitQueryLoop

Spec == Init /\ [][Next]_vars
         /\ WF_vars(SendQuery) /\ WF_vars(ReplyAndAdopt)
         /\ WF_vars(TallyReplies) /\ WF_vars(ExitQueryLoop)

\* Color assignment is always a valid color or uncolored, and the message set
\* only ever contains well-formed messages of the tags Slush defines.
TypeInvariant == TypeOK

\* Every process in the system eventually reaches its terminal state.
EventualTermination == \A p \in SlushProcess: ProcessDone(p)
====