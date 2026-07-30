---- MODULE MCBoulanger ----
EXTENDS Naturals

\* Finite override: the natural numbers are restricted to the range 0..MaxNat.
CONSTANTS N, MaxNat, Nat

NONE == "none"

VARIABLES loc, pc, ticket, done

vars == <<loc, pc, ticket, done>>

\* loc: the critical-section location of each process (an integer).
\* pc: the control phase of each process.
\* ticket: the bakery ticket number each process currently holds (Nat).
\* done: a flag whether each process has entered the critical section.
TypeOK ==
  /\ loc \in [1..N -> 0..3]
  /\ pc \in [1..N -> {"idle", "waiting", "cs"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ done \in [1..N -> BOOLEAN]

Init ==
  /\ loc = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ done = [i \in 1..N |-> FALSE]

Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = 1 + Cardinality({j \in 1..N : pc[j] = "waiting"})]
  /\ UNCHANGED <<loc, done>>

Enter(i) ==
  /\ pc[i] = "waiting"
  /\ \A j \in 1..N : (pc[j] = "cs") => (ticket[i] < ticket[j])
  /\ loc' = [loc EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ done' = [done EXCEPT ![i] = TRUE]
  /\ UNCHANGED ticket

Exit(i) ==
  /\ pc[i] = "cs"
  /\ loc' = [loc EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, done>>

Next == \E i \in 1..N : Request(i) \/ Enter(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: a process may be in the critical section only if its loc
\* marker says it is there, and at most one process is ever in it.
MutualExclusion ==
  /\ \A i \in 1..N : pc[i] = "cs" => loc[i] = 1
  /\ Cardinality({i \in 1..N : pc[i] = "cs"}) <= 1

\* The full inductive invariant is the conjunction of all three properties.
Inv == MutualExclusion /\ TypeOK

\* The finite-number state constraint: no ticket has reached the maximum.
BoundedCapacity == \A i \in 1..N : ticket[i] < MaxNat

====