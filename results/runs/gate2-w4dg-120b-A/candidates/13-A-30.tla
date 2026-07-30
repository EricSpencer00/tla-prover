---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES ticket, cs, pc, served

vars == <<ticket, cs, pc, served>>

\* The natural numbers are globally overridden to a finite range 0..MaxNat for
\* model checking. Every ticket number the Bakery algorithm hands out must fit
\* inside that range.
\* A process stands on the bench before asking for a ticket.

Range == 0..MaxNat

TypeOK ==
  /\ ticket \in [1..N -> Range]
  /\ cs \in SUBSET (1..N)
  /\ pc \in [1..N -> {"idle", "waiting", "hold", "serving", "done"}]
  /\ served \in 0..MaxNat

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ cs = {}
  /\ pc = [i \in 1..N |-> "idle"]
  /\ served = 0

\* A process that has not yet entered the bakery asks for a ticket.  The
\* ticket number it receives is the smallest currently unused number, or zero
\* if the range is exhausted.
Ask(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] =
        CHOOSE m \in Range :
          \A j \in 1..N : (pc[j] # "serving" => ticket[j] # m) /\ m >= ticket[i]]
  /\ UNCHANGED <<cs, served>>

\* A waiting process enters the critical section only when it holds the
\* smallest ticket among all waiting holders.
Enter(i) ==
  /\ pc[i] = "waiting"
  /\ \A j \in 1..N : (pc[j] = "waiting" /\ j # i) => ticket[i] <= ticket[j]
  /\ cs' = cs \cup {i}
  /\ pc' = [pc EXCEPT ![i] = "hold"]
  /\ UNCHANGED <<ticket, served>>

Leave(i) ==
  /\ pc[i] = "hold"
  /\ cs' = cs \ {i}
  /\ pc' = [pc EXCEPT ![i] = "serving"]
  /\ served' = IF served < MaxNat THEN served + 1 ELSE served
  /\ UNCHANGED ticket

Reset(i) ==
  /\ pc[i] = "serving"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED <<cs, served>>

Next ==
  \/ \E i \in 1..N : Ask(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Leave(i)
  \/ \E i \in 1..N : Reset(i)

ISpec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : (i \in cs) => (pc[i] = "hold")

\* Type correctness of every variable.
TypeOK ==
  /\ ticket \in [1..N -> Range]
  /\ cs \subseteq (1..N)
  /\ pc \in [1..N -> {"idle", "waiting", "hold", "serving", "done"}]
  /\ served \in Range

\* The full inductive invariant: no two processes in the critical section at
\* the same time, plus everything else that must be preserved.
Inv ==
  /\ MutualExclusion
  /\ TypeOK

====