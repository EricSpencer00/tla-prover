---- MODULE Slush ----
EXTENDS Naturals

Nodes == {1, 2, 3}

Messages == [kind: {"query", "reply", "termination"}, src: 1..3, dst: 1..3, clr: {"red", "blue", "nocolor"}]

VARIABLES color, msgs, pc, sample, iterations

vars == <<color, msgs, pc, sample, iterations>>

\* The process topology is encoded as a set of triples (node, loopProc, queryProc)
\* so the two process types stay tied to the node they serve.
Hosts == {<<1, 1, 1>>, <<2, 2, 2>>, <<3, 3, 3>>}

\* Message creation is a pure record function, so the no-message sentinel must be
\* fixed up to a concrete value here rather than in Init.
NoMessage == [kind |-> "termination", src |-> 1, dst |-> 1, clr |-> "nocolor"]

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

ColorCount(n, clr) == SumOver(UNION { IF src \in S /\ clr = "red" THEN {src} ELSE {} : S \in sample[n] }, Nodes)

TypeOK ==
  /\ color \in [Nodes -> {"red", "blue", "nocolor"}]
  /\ msgs \subseteq Messages
  /\ pc \in [1..3 -> {"preparing", "querying", "counting", "done"}]
  /\ sample \in [1..3 -> SUBSET SUBSET Nodes]
  /\ iterations \in [1..3 -> 0..1]

Init ==
  /\ color = [n \in Nodes |-> "nocolor"]
  /\ msgs = {}
  /\ pc = [p \in 1..3 |-> "preparing"]
  /\ sample = [p \in 1..3 |-> {}]
  /\ iterations = [p \in 1..3 |-> 0]

\* The client assigns an initial color, which can never be changed later.
ClientAssignColor ==
  \E n \in Nodes, clr \in {"red", "blue"} :
     /\ color[n] = "nocolor"
     /\ color' = [color EXCEPT ![n] = clr]
     /\ UNCHANGED <<msgs, pc, sample, iterations>>

RequireColor ==
  \E p \in 1..3, n \in Nodes :
    /\ <<n, p, n>> \in Hosts
    /\ pc[p] = "preparing"
    /\ color[n] # "nocolor"
    /\ pc' = [pc EXCEPT ![p] = "querying"]
    /\ UNCHANGED <<color, msgs, sample, iterations>>

QuerySampleSet ==
  \E p \in 1..3, n \in Nodes :
    /\ <<n, p, n>> \in Hosts
    /\ pc[p] = "querying"
    /\ Cardinality(sample[p]) < 2
    /\ \E q \in Nodes :
         /\ q # n
         /\ q \notin sample[p]
         /\ LET m == [kind |-> "query", src |-> p, dst |-> q, clr |-> color[n]] IN msgs' = msgs \cup {m}
         /\ sample' = [sample EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED <<color, pc, iterations>>

RespondQuery ==
  \E m \in msgs :
    /\ m.kind = "query"
    /\ LET reply == [kind |-> "reply", src |-> m.dst, dst |-> m.src, clr |> IF color[m.dst] = "nocolor" THEN m.clr ELSE color[m.dst]] IN
         msgs' = (msgs \ {m}) \cup {reply}
    /\ color' = IF color[m.dst] = "nocolor" THEN [color EXCEPT ![m.dst] = m.clr] ELSE color
    /\ UNCHANGED <<pc, sample, iterations>>

TallyReplies ==
  \E p \in 1..3, n \in Nodes :
    /\ <<n, p, n>> \in Hosts
    /\ pc[p] = "querying"
    /\ Cardinality(sample[p]) = 2
    /\ \A q \in sample[p] : \E m \in msgs : m.kind = "reply" /\ m.dst = p /\ m.src = q
    /\ LET reds == Cardinality({q \in sample[p] : \E m \in msgs : m.kind = "reply" /\ m.dst = p /\ m.src = q /\ m.clr = "red"})
           blues == Cardinality({q \in sample[p] : \E m \in msgs : m.kind = "reply" /\ m.dst = p /\ m.src = q /\ m.clr = "blue"}) IN
         color' = [color EXCEPT ![n] = IF reds >= 2 THEN "red" ELSE IF blues >= 2 THEN "blue" ELSE color[n]]
    /\ pc' = [pc EXCEPT ![p] = "counting"]
    /\ UNCHANGED <<msgs, sample, iterations>>

LoopTermination ==
  \E p \in 1..3 :
    /\ pc[p] = "counting"
    /\ iterations[p] < 1
    /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ msgs' = msgs \cup {[kind |-> "termination", src |-> p, dst |-> p, clr |-> "nocolor"]}
    /\ UNCHANGED <<color, sample>>

QueryLoopExit ==
  /\ \A q \in Nodes : <<q, q, q>> \in Hosts
  /\ \A p \in 1..3 : pc[p] = "done"
  /\ UNCHANGED vars

Next ==
  \/ ClientAssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ClientAssignColor)
  /\ WF_vars(QuerySampleSet)
  /\ WF_vars(RespondQuery)
  /\ WF_vars(TallyReplies)

TypeInvariant == TypeOK

Termination == \A p \in 1..3 : pc[p] = "done"

====