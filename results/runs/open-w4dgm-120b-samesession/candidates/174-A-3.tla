---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess,
  HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

Action == {"pick", "reply", "exit"}
MessageType == [kind: Action, src: Node, dst: Node, color: {NoColor} \cup {"red", "blue"}]

\* Query messages still in flight; replies are put into the same pool so
\* a loop process can pick them up in any order.
Variable color, inbox, pc, sample, iteration

vars == <<color, inbox, pc, sample, iteration>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup {"red", "blue"}]
  /\ inbox \subseteq MessageType
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "waiting", "sampling", "counting", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "idle"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iteration = [p \in SlushLoopProcess |-> 0]

Quiescent ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \A p \in SlushQueryProcess : pc[p] = "done"

RequestColor ==
  \E n \in Node :
    /\ color[n] = NoColor
    /\ \E c \in {"red", "blue"} : color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<inbox, pc, sample, iteration>>

RequireColor ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "idle"
    /\ LET n == CHOOSE n \in Node : <<n, p, "loop">> \in HostMapping
       IN \E c \in {"red", "blue"} :
            /\ color[n] = c
            / pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<color, inbox, sample, iteration>>

SendQuery ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "waiting"
    /\ LET n == CHOOSE n \in Node : <<n, p, "loop">> \in HostMapping
           c == color[n]
           peers == (Node \ {n})
           peers' == IF Cardinality(peers) <= SampleSetSize
                      THEN peers
                      ELSE CHOOSE S \in SUBSET peers :
                                /\ Cardinality(S) = SampleSetSize
                                /\ \A q \in S : <<q, p, "query">> \in HostMapping
           msgs == {[kind |-> "pick", src |-> n, dst |-> q, color |-> c] : q \in peers'}
       IN /\ inbox' = inbox \cup msgs
          /\ sample' = [sample EXCEPT ![p] = peers']
    /\ pc' = [pc EXCEPT ![p] = "sampling"]
    /\ UNCHANGED <<color, iteration>>

\* A query target adopts the query's color if it has none yet.
RespondQuery ==
  \E m \in inbox :
    /\ m.kind = "pick"
    /\ LET q == CHOOSE q \in SlushQueryProcess : <<m.dst, q, "query">> \in HostMapping
       IN /\ color' = [color EXCEPT ![m.dst] = IF color[m.dst] = NoColor THEN m.color ELSE color[m.dst]]
          /\ inbox' = (inbox \ {m})
                 \cup {[kind |-> "reply", src |-> m.dst, dst |-> m.src, color |-> IF color[m.dst] = NoColor THEN m.color ELSE color[m.dst]]}
    /\ UNCHANGED <<pc, sample, iteration>>

TallyReplies ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "sampling"
    /\ LET replies == {m \in inbox : m.kind = "reply" /\ m.dst = p /\ m.src \in sample[p]}
           reds == Cardinality({m \in replies : m.color = "red"})
           blues == Cardinality({m \in replies : m.color = "blue"})
           n == CHOOSE n \in Node : <<n, p, "loop">> \in HostMapping
           newcol == IF reds >= PickFlipThreshold THEN "red"
                      ELSE IF blues >= PickFlipThreshold THEN "blue"
                      ELSE color[n]
           inbox' == inbox \ replies
                       \cup {[kind |-> "counted", src |-> n, dst |-> p, color |-> newcol]}
       IN /\ color' = [color EXCEPT ![n] = newcol]
          /\ inbox' = inbox'
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = IF iteration[p] + 1 >= SlushIterationCount THEN "done" ELSE "counting"]

LoopDone ==
  \E p \in SlushLoopProcess :
    /\ pc[p] \in {"counting", "done"}
    /\ pc[p] = "done"
    /\ \A q \in SlushLoopProcess : pc[q] = "done"
    /\ inbox' = inbox \cup {[kind |-> "exit", src |-> p, dst |-> p, color |-> NoColor]}
    /\ UNCHANGED <<color, pc, sample, iteration>>

QueryDone ==
  \E q \in SlushQueryProcess :
    /\ pc[q] \in {"idle", "done"}
    /\ pc[q] = "idle"
    /\ \A p \in SlushLoopProcess : pc[p] = "done"
    /\ pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<color, inbox, sample, iteration>>

Next ==
  \/ RequestColor
  \/ RequireColor
  \/ SendQuery
  \/ RespondQuery
  \/ TallyReplies
  \/ LoopDone
  \/ QueryDone

Spec == Init /\ [][Next]_vars /\ WF_vars(RequireColor) /\ WF_vars(SendQuery)
          /\ WF_vars(RespondQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopDone) /\ WF_vars(QueryDone)

TypeInvariant == TypeOK

Termination == Quiescent
====