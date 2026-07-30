---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES group, loc, inbox, sent, started
vars == <<group, loc, inbox, sent, started>>

Correct == group[1]
Faulty == group[2]

Msgs == {<<"ECHO", p>> : p \in 1 .. N}

RECURSIVE EchoCount(_, _)
EchoCount(m, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
           rest == EchoCount(m, S \ {x})
       IN IF m \in inbox[x] THEN rest + 1 ELSE rest

TypeOK ==
  /\ group \in [1..2 -> SUBSET (1..N)]
  /\ loc \in [1..N -> {"noget", "noecho", "sent", "done"}]
  /\ inbox \in [1..N -> SUBSET Msgs]
  /\ sent \subseteq Msgs
  /\ started \in BOOLEAN

FCConstraints ==
  /\ Cardinality(Correct) = N - F
  /\ group[1] \cup group[2] = 1..N
  /\ group[1] \cap group[2] = {}
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

Init ==
  /\ group = [1 |-> {}, 2 |-> {}]
  /\ loc = [p \in 1..N |-> IF started THEN "noget" ELSE "noecho"]
  /\ inbox = [p \in 1..N |-> {}]
  /\ sent = {}
  /\ started \in BOOLEAN

InitsOnly ==
  /\ group = [1 |-> {}, 2 |-> {}]
  /\ loc = [p \in 1..N |-> "noecho"]
  /\ inbox = [p \in 1..N |-> {}]
  /\ sent = {}
  /\ started = FALSE

Receive(p) ==
  /\ p \in Correct
  /\ loc[p] \in {"noget", "noecho"}
  /\ \E S \in SUBSET (sent \cup Msgs) :
       inbox' = [inbox EXCEPT ![p] = @ \cup S]
  /\ UNCHANGED <<group, loc, sent, started>>

SendEcho(p) ==
  /\ p \in Correct
  /\ loc[p] = "noget"
  /\ inbox[p] # {}
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {<<"ECHO", p>>}
  /\ UNCHANGED <<group, inbox, started>>

EchoPrompt(p) ==
  /\ p \in Correct
  /\ loc[p] = "noecho"
  /\ EchoCount(<<"ECHO", p>>, Correct) >= N - 2 * T
  /\ EchoCount(<<"ECHO", p>>, Correct) < N - T
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {<<"ECHO", p>>}
  /\ UNCHANGED <<group, inbox, started>>

ForceAccept(p) ==
  /\ p \in Correct
  /\ loc[p] = "noecho"
  /\ EchoCount(<<"ECHO", p>>, Correct) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {<<"ECHO", p>>}
  /\ UNCHANGED <<group, inbox, started>>

ReceiveEcho(p) ==
  /\ p \in Correct
  /\ loc[p] = "sent"
  /\ EchoCount(<<"ECHO", p>>, Correct) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<group, inbox, sent, started>>

Next ==
  \/ \E p \in 1..N : Receive(p)
  \/ \E p \in 1..N : SendEcho(p)
  \/ \E p \in 1..N : EchoPrompt(p)
  \/ \E p \in 1..N : ForceAccept(p)
  \/ \E p \in 1..N : ReceiveEcho(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : Receive(p))
  /\ WF_vars(\E p \in 1..N : SendEcho(p))

CorrLtl ==
  /\ started
  /\ <>(\A p \in Correct : loc[p] = "done")

RelayLtl ==
  /\ (\E p \in Correct : loc[p] = "done") ~> (\A p \in Correct : loc[p] = "done")

UnforgLtl ==
  /\ ~started
  /\ (\A p \in Correct : loc[p] = "done")

====