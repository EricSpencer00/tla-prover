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

MessageIds == {"query", "reply", "done"}

VARIABLES color, inbox, pstate, sample, iterations

vars == <<color, inbox, pstate, sample, iterations>>

RECURSIVE Count(_, _)
Count(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN IF f[x] THEN 1 + Count(f, S \ {x}) ELSE Count(f, S \ {x})

TypeOK ==
  /\ color \in [Node -> {NoColor} \union {0, 1}]
  /\ inbox \in SUBSET [id: MessageIds, to: SlushQueryProcess \union SlushLoopProcess, from: SlushLoopProcess \union SlushQueryProcess, payload: {NoColor} \union {0, 1}]
  /\ pstate \in [SlushLoopProcess -> {"waiting", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pstate = [l \in SlushLoopProcess |-> "waiting"]
  /\ sample = [l \in SlushLoopProcess |-> {}]
  /\ iterations = [l \in SlushLoopProcess |-> 0]

AssignColor ==
  /\ \E n \in Node, col \in {0, 1}:
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = col]
  /\ UNCHANGED <<inbox, pstate, sample, iterations>>

RequireColor ==
  /\ \E l \in SlushLoopProcess:
       /\ pstate[l] = "waiting"
       /\ \E n \in Node:
            /\ [lp |-> l, qp |-> l, node |-> n] \in HostMapping
            /\ color[n] # NoColor
            /\ pstate' = [pstate EXCEPT ![l] = "sampling"]
  /\ UNCHANGED <<color, inbox, sample, iterations>>

QuerySampleSet ==
  /\ \E l \in SlushLoopProcess:
       /\ pstate[l] = "sampling"
       /\ iterations[l] < SlushIterationCount
       /\ \E S \in SUBSET SlushQueryProcess:
            /\ Cardinality(S) = SampleSetSize
            /\ \A q \in S: ~ q \in sample[l]
            /\ inbox' = inbox \union
                 {[id |-> "query", to |-> q, from |-> l, payload |-> color[[lp |-> l, qp |-> l, node |-> "unknown"].node] : q \in S]
            /\ sample' = [sample EXCEPT ![l] = S]
  /\ UNCHANGED <<color, pstate, iterations>>

RespondToQuery ==
  /\ \E q \in SlushQueryProcess, l \in SlushLoopProcess:
       /\ [id |-> "query", to |-> q, from |-> l, payload |-> NoColor] \in inbox
       /\ inbox' = (inbox \ {[id |-> "query", to |-> q, from |-> l, payload |-> NoColor]})
                    \union
                    {[id |-> "reply", to |-> l, from |-> q, payload |-> LET n == [lp |-> l, qp |-> q, node |-> "unknown"].node
                                                                    IN IF color[n] = NoColor THEN payload ELSE color[n]]}
       /\ color' = IF color[[lp |-> l, qp |-> q, node |-> "unknown"].node] = NoColor
                   THEN [color EXCEPT ![[lp |-> l, qp |-> q, node |-> "unknown"].node] = payload]
                   ELSE color
  /\ UNCHANGED <<pstate, sample, iterations>>

TallyReplies ==
  /\ \E l \in SlushLoopProcess:
       /\ pstate[l] = "sampling"
       /\ Cardinality({q \in sample[l] : [id |-> "reply", to |-> l, from |-> q, payload |-> NoColor] \in inbox}) = SampleSetSize
       /\ LET countArray ==
            [col \in {0, 1} |-> Count([q \in SlushQueryProcess |-> [id |-> "reply", to |-> l, from |-> q, payload |-> col] \in inbox], SlushQueryProcess)]
          IN color' = IF Count([c \in {0, 1} |-> countArray[c] >= PickFlipThreshold], {0, 1}) = 1
                      THEN LET col == CHOOSE c \in {0, 1} : countArray[c] >= PickFlipThreshold
                           IN [color EXCEPT ![[lp |-> l, qp |-> l, node |-> "unknown"].node] = col]
                      ELSE color
       /\ inbox' = inbox \ {[id |-> "reply", to |-> l, from |-> q, payload |-> NoColor] : q \in sample[l]}
       /\ sample' = [sample EXCEPT ![l] = {}]
       /\ iterations' = [iterations EXCEPT ![l] = IF iterations[l] < SlushIterationCount THEN @ + 1 ELSE @]
       /\ pstate' = [pstate EXCEPT ![l] = IF iterations[l] + 1 >= SlushIterationCount THEN "done" ELSE "sampling"]

LoopTermination ==
  /\ \E l \in SlushLoopProcess:
       /\ pstate[l] = "tallying"
       /\ pstate' = [pstate EXCEPT ![l] = "done"]
       /\ inbox' = inbox \union {[id |-> "done", to |-> l, from |-> l, payload |-> NoColor]}
  /\ UNCHANGED <<color, sample, iterations>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess:
       /\ \A l \in SlushLoopProcess: [id |-> "done", to |-> l, from |-> l, payload |-> NoColor] \in inbox
       /\ pstate' = [pstate EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, inbox, sample, iterations>>

Next ==
  \/ AssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

AllDone ==
  /\ \A l \in SlushLoopProcess: pstate[l] = "done"
  /\ \A q \in SlushQueryProcess: pstate[q] = "done"

====