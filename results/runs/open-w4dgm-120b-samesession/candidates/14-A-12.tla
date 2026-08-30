---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES serving, want, ticket, free, inCS

vars == <<serving, want, ticket, free, inCS>>

\* The override makes Nat a bounded, checkable version of the infinite
\* naturals; every specification below uses it instead of the true Nat.
Nat == 0..MaxNat

InUse == \E i \in 1..N : inCS[i]

TypeOK ==
  /\ serving \in {0} \cup Nat
  /\ want \in 0..N
  /\ ticket \in [1..N -> Nat]
  /\ free \in Nat
  /\ inCS \in [1..N -> BOOLEAN]

Init ==
  /\ serving = 0
  /\ want = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ free = 0
  /\ inCS = [i \in 1..N |-> FALSE]

\* A process asks for the critical resource, taking the next free ticket.
Bump(i) ==
  /\ want < N
  /\ ~inCS[i]
  /\ want' = want + 1
  /\ ticket' = [ticket EXCEPT ![i] = want + 1]
  /\ UNCHANGED <<serving, free, inCS>>

\* Entry is decided by the single compare-and-swap on the shared register:
\* it succeeds only if the register is free and the process's ticket is
\* exactly the next in sequence.
Enter(i) ==
  /\ free < want
  /\ serving = 0
  /\ ticket[i] = free + 1
  /\ serving' = i
  /\ free' = free + 1
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<want, ticket>>

\* Leaving frees the register for the next ticket holder.
Leave(i) ==
  /\ inCS[i]
  /\ serving' = 0
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<want, ticket, free>>

Next ==
  \/ \E i \in 1..N : Bump(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Leave(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == ~InUse

Inv ==
  /\ serving # 0 => inCS[serving]
  /\ (\A i \in 1..N : inCS[i]) => serving = i

\* The model is bounded to keep it finite: no process may ever reach the
\* maximum natural number for its ticket, because the register runs out
\* before the sequence can get there.
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====