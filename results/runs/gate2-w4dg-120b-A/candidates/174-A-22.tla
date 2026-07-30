---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

Cap == Cardinality(Node)

\* Two colors, identified by two distinct members of the node set.
ColorA == CHOOSE n \in Node : TRUE
ColorB == CHOOSE n \in Node : (n # ColorA)

ColorDomain == {ColorA, ColorB, NoColor}

\* All messages in flight, labelled by kind; this is the only place messages
\* live, so every message must appear here.
Message ==
  [kind : {"query", "queryReply", "termination"},
   from : SlushQueryProcess \cup SlushLoopProcess,
   to   : SlushLoopProcess \cup SlushQueryProcess,
   payload : ColorDomain]

RECURSIVE CountColor(_)
CountColor(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN (IF x.payload = ColorA THEN 1 ELSE 0)
       + CountColor(S \ {x})

VARIABLES
  color,        \* Color assignment: [Node -> ColorDomain]
  messages,     \* Set of in-flight messages: SUBSET Message
  pc,           \* Process program counters: [SlushLoopProcess \cup SlushQueryProcess -> {"awaitingColor", "querying", "tallying", "done", "replyLoop"}]
  sampleSet,    \* Random subsets under active queries, per loop process
  iters         \* Iteration counter, per loop process

vars == <<color, messages, pc, sampleSet, iters>>

TypeInvariant ==
  /\ color \in [Node -> ColorDomain]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"awaitingColor", "querying", "tallying", "done", "replyLoop"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> IF p \in SlushLoopProcess THEN "awaitingColor" ELSE "replyLoop"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

AssignColor ==
  \E n \in Node:
    /\ color[n] = NoColor
    /\ \E c \in {ColorA, ColorB}: color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sampleSet, iters>>

RequireColor ==
  \E lp \in SlushLoopProcess:
    /\ pc[lp] = "awaitingColor"
    /\ \E n \in Node:
         /\ [process |-> lp, host |-> n] \in HostMapping
         /\ color[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "querying"]
    /\ UNCHANGED <<color, messages, sampleSet, iters>>

QuerySample ==
  \E lp \in SlushLoopProcess:
    /\ pc[lp] = "querying"
    /\ iters[lp] < SlushIterationCount
    /\ \E peers \in SUBSET SlushQueryProcess:
         /\ peers # {}
         /\ Cardinality(peers) <= SampleSetSize
         /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
         /\ messages' = messages \cup
              {[kind |-> "query", from |-> lp, to |-> qp, payload |-> color[[p \in HostMapping |-> p][lp]] : qp \in peers]
  /\ pc' = [pc EXCEPT ![lp] = "tallying"]
    /\ UNCHANGED <<color, iters>>

\* A query process adopts the query color when uncolored, then replies.
RespondToQuery ==
  \E qp \in SlushQueryProcess:
    /\ \E m \in messages:
         /\ m.kind = "query"
         /\ m.to = qp
         /\ LET n == [p \in HostMapping |-> p][qp] IN
              /\ color' = IF color[n] = NoColor THEN [color EXCEPT ![n] = m.payload] ELSE color
              /\ messages' = (messages \ {m})
                 \cup {[kind |-> "queryReply", from |-> qp, to |-> m.from, payload |-> IF color[n] = NoColor THEN m.payload ELSE color[n]]}
    /\ UNCHANGED <<pc, sampleSet, iters>>

TallyReplies ==
  \E lp \in SlushLoopProcess:
    /\ pc[lp] = "tallying"
    /\ \A qp \in sampleSet[lp]: \E m \in messages: m.kind = "queryReply" /\ m.from = qp
    /\ LET replies == {m \in messages : m.kind = "queryReply" /\ m.from \in sampleSet[lp]} IN
         /\ color' = IF CountColor(replies) >= PickFlipThreshold
                       THEN [color EXCEPT ![[p \in HostMapping |-> p][lp]] = ColorA]
                       ELSE color
         /\ messages' = messages \ {m \in replies}
    /\ pc' = [pc EXCEPT ![lp] = "awaitingColor"]
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ iters' = [iters EXCEPT ![lp] = iters[lp] + 1]

LoopTerminate ==
  \E lp \in SlushLoopProcess:
    /\ pc[lp] \in {"awaitingColor", "querying", "tallying"}
    /\ iters[lp] = SlushIterationCount
    /\ pc' = [pc EXCEPT ![lp] = "done"]
    /\ messages' = messages \cup {[kind |-> "termination", from |-> lp, to |-> NoMessage, payload |-> NoColor]}
    /\ UNCHANGED <<color, sampleSet, iters>>

QueryLoopExit ==
  \E qp \in SlushQueryProcess:
    /\ pc[qp] = "replyLoop"
    /\ \A lp \in SlushLoopProcess: [kind |-> "termination", from |-> lp, to |-> NoMessage, payload |-> NoColor] \in messages
    /\ pc' = [pc EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<color, messages, sampleSet, iters>>

Next ==
  \/ AssignColor
  \/ RequireColor
  \/ QuerySample
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTerminate
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

Termination ==
  \A p \in SlushLoopProcess \cup SlushQueryProcess: <>(pc[p] = "done")

====