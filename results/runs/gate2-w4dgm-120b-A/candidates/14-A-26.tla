---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

VARIABLES ticket, inCS, waiting, nextTicket
vars == <<ticket, inCS, waiting, nextTicket>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ waiting \in SUBSET (1..N)
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ ticket = [p \in 1..N |-> 0]
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ waiting = {}
  /\ nextTicket = 0

Request(p) ==
  /\ p \notin waiting
  /\ ~inCS[p]
  /\ waiting' = waiting \cup {p}
  /\ UNCHANGED <<ticket, inCS, nextTicket>>

Enter(p) ==
  /\ p \in waiting
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ waiting' = waiting \ {p}
  /\ UNCHANGED inCS

EnterAny == \E p \in 1..N : Enter(p)

Begin(p) ==
  /\ ticket[p] > 0
  /\ \A q \in 1..N : ~inCS[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, waiting, nextTicket>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<waiting, nextTicket>>

FinishAny == \E p \in 1..N : Exit(p)

Next == \E p \in 1..N : Request(p) \/ Enter(p) \/ Begin(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(EnterAny) /\ WF_vars(FinishAny)

MutualExclusion ==
  \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => (p = q)

Inv ==
  /\ \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => (p = q)
  /\ SumOver(ticket, 1..N) <= SumOver([p \in 1..N |-> MaxNat], 1..N)

TicketBound == \A p \in 1..N : ticket[p] < MaxNat

====