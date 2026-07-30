---- MODULE Slush ----
EXTENDS Integers, FiniteSets

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

\* Slush loop processes drive the protocol by sampling peers and flipping colors.
\* Slush query processes respond to peer queries, adopting the query color if
\* uncolored. A client process assigns initial colors to uncolored nodes.
\* All state is captured in a single record that the next-state relation
\* updates; PlusCal would normally generate this, but it is written by hand
\* here to match the required identifier set exactly.

VARIABLES colorMap, messages, pc, sample, iters

vars == <<colorMap, messages, pc, sample, iters>>

Message == [kind : {"query", "reply", "term"}, src : Node, dst : Node, col : Node \cup {NoColor}]

Init ==
  /\ colorMap = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage} |-> "idle"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

AssignColor ==
  \E n \in Node, c \in {NoColor} \cup Node :
    /\ colorMap[n] = NoColor
    /\ colorMap' = [colorMap EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sample, iters>>

RequireColor ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "idle"
    /\ colorMap[p] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "sampling"]
    /\ UNCHANGED <<colorMap, messages, sample, iters>>

\* A loop process selects a random sample of peers and queries their color.
QuerySampleSet ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "sampling"
    /\ Cardinality(sample[p]) < SampleSetSize
    /\ \E q \in SlushQueryProcess :
         /\ q \notin sample[p]
         /\ colorMap[p] # NoColor
         /\ sample' = [sample EXCEPT ![p] = @ \cup {q}]
         /\ messages' = messages \cup {[kind |-> "query", src |-> p, dst |-> q, col |-> colorMap[p]]}
    /\ UNCHANGED <<colorMap, pc, iters>>

\* A query process adopts the query's color if it is currently uncolored, then
\* replies with whatever color it now holds.
RespondToQuery ==
  \E m \in messages :
    /\ m.kind = "query"
    /\ m.dst \notin sample[m.src]
    /\ colorMap' = [colorMap EXCEPT ![m.dst] =
                      IF colorMap[m.dst] = NoColor THEN m.col ELSE colorMap[m.dst]]
    /\ messages' = (messages \ {m})
                    \cup {[kind |-> "reply", src |-> m.dst, dst |-> m.src, col |-> colorMap[m.dst]]}
    /\ UNCHANGED <<pc, sample, iters>>

\* The loop process tallies replies and flips its node's color if an opinion
\* reaches the flip threshold.
TallyReplies ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "sampling"
    /\ \A q \in sample[p] : \E m \in messages : m.kind = "reply" /\ m.src = q /\ m.dst = p
    /\ LET replies == {m \in messages : m.kind = "reply" /\ m.dst = p}
           tallies == [c \in {NoColor} \cup Node |-> Cardinality({m \in replies : m.col = c})]
       IN \/ \E c \in Node : tallies[c] >= PickFlipThreshold /\ colorMap' = [colorMap EXCEPT ![p] = c]
          \/ (colorMap' = colorMap)
    /\ messages' = messages \ {m \in messages : m.kind = "reply" /\ m.dst = p}
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = IF iters[p] + 1 >= SlushIterationCount THEN "done" ELSE "idle"]

LoopTermination ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "done"
    /\ \A q \in SlushLoopProcess : pc[q] = "done"
    /\ messages' = messages \cup {[kind |-> "term", src |-> NoMessage, dst |-> p, col |-> NoColor]}
    /\ pc' = [pc EXCEPT ![p] = "exited"]
    /\ UNCHANGED <<colorMap, sample, iters>>

QueryLoopExit ==
  \E q \in SlushQueryProcess :
    /\ pc[q] = "idle"
    /\ \A p \in SlushLoopProcess : pc[p] = "exited"
    /\ pc' = [pc EXCEPT ![q] = "exited"]
    /\ UNCHANGED <<colorMap, messages, sample, iters>>

Next ==
  \/ AssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ colorMap \in [Node -> {NoColor} \cup Node]
  /\ \A m \in messages : m.kind \in {"query", "reply", "term"}

====