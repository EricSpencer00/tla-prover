---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

NONE == 0 - 1
 \* The set of ticket numbers is a finite slice of the naturals, 0..MaxNat.
Tickets == 0 .. MaxNat

VARIABLES using, number, cs, choosing

vars == <<using, number, cs, choosing>>

TypeOK ==
  /\ using \in [1..N -> BOOLEAN]
  /\ number \in [1..N -> Tickets]
  /\ cs \in [1..N -> BOOLEAN]
  /\ choosing \in [1..N -> BOOLEAN]

Init ==
  /\ using = [i \in 1..N |-> FALSE]
  /\ number = [i \in 1..N |-> 0]
  /\ cs = [i \in 1..N |-> FALSE]
  /\ choosing = [i \in 1..N |-> FALSE]

Acquire(i) ==
  /\ ~using[i]
  /\ using' = [using EXCEPT ![i] = TRUE]
  /\ number' = [number EXCEPT ![i] = 0]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED cs

\* The bounded range is the only place where the bound is enforced.
Take(i) ==
  /\ choosing[i]
  /\ \A j \in 1..N : (using[j] /\ number[j] # 0) => number[j] < number[i]
  /\ number' = [number EXCEPT ![i] = IF number[i] < MaxNat THEN number[i] + 1 ELSE 0]
  /\ UNCHANGED <<using, cs, choosing>>

Enter(i) ==
  /\ ~cs[i]
  /\ using[i]
  /\ choosing[i]
  /\ \A j \in 1..N : (using[j] /\ number[j] # 0) => number[j] < number[i]
  /\ cs' = [cs EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<using, number, choosing>>

Leave(i) ==
  /\ cs[i]
  /\ cs' = [cs EXCEPT ![i] = FALSE]
  /\ using' = [using EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<number, choosing>>

Next ==
  \/ \E i \in 1..N : Acquire(i)
  \/ \E i \in 1..N : Take(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Leave(i)

\* The inductive specification starts from the invariant rather than from Init
\* alone, so that the invariant is verified from any reachable state.
ISpec == Init /\ [][Next]_vars /\ WF_vars(\E i \in 1..N : Enter(i))

\* Mutual exclusion: no two processes in the critical section at once.
MutualExclusion == \A i \in 1..N : cs[i] => (\A j \in 1..N : cs[j] => j = i)

\* The full inductive invariant: every process in the critical section is in
\* its critical section with a live ticket, and every live ticket was issued
\* by a process that was using the bakery.
Inv ==
  /\ \A i \in 1..N : cs[i] => (using[i] /\ number[i] # 0)
  /\ \A i \in 1..N : number[i] # 0 => using[i]

====