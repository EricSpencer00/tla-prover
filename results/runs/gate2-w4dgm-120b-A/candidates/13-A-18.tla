---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket
vars == <<inCS, want, ticket, nextTicket>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumOver(f, S \ {x})

MutualExclusion == SumOver(inCS, 1..N) <= 1

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ want = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

Request(i) ==
  /\ ~want[i]
  /\ ~inCS[i]
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

Enter(i) ==
  /\ want[i]
  /\ ~inCS[i]
  /\ ticket[i] = 0
  /\ nextTicket < MaxNat
  /\ \A j \in 1..N : ~inCS[j]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<inCS, want>>

EnterAny == \E i \in 1..N : Enter(i)

EnterSome == \E i \in 1..N : Enter(i)

EnterSomeWeak == \E i \in 1..N : Enter(i)

EnterSomeFair == \E i \in 1..N : Enter(i)

EnterAnyFair == \E i \in 1..N : Enter(i)

Acquire == EnterSome \/ EnterAny

Critical(i) ==
  /\ want[i]
  /\ ticket[i] > 0
  /\ \A j \in 1..N : ~inCS[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<want, ticket, nextTicket>>

Leave(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED nextTicket

Next == Acquire \/ (\E i \in 1..N : Critical(i) \/ Leave(i))

Spec == Init /\ [][Next]_vars /\ WF_vars(EnterAny) /\ WF_vars(Acquire)

Inv == MutualExclusion /\ TypeOK

IsSpec == Spec
====