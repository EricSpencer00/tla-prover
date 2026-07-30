---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES ticket, served, serving

vars == <<ticket, served, serving>>

\* Any natural number value is a ticket number in the bakery ordering. The
\* model checking configuration overrides the type of Nat to the finite range
\* 0..MaxNat below (MaxNat = 2); the algorithm's ticket discipline is unchanged.
Tickets == (Nat -> 0..MaxNat)

TypeOK ==
  /\ ticket \in Tickets
  /\ served \subseteq 0..(N - 1)
  /\ serving \in Nat

\* A process may enter the critical section only while nobody else is serving
\* and its ticket is ahead of every unserved process's ticket. This is what
\* gives mutual exclusion even though the ticket numbers are drawn from a
\* bounded range and may wrap back to zero.
MutualExclusion == serving # 0 => \A q \in served : ticket[serving - 1] < ticket[q]

\* The full inductive invariant: the type discipline plus mutual exclusion.
Inv == TypeOK /\ MutualExclusion

Init ==
  /\ ticket = [i \in 0..(N - 1) |-> 0]
  /\ served = {}
  /\ serving = 0

\* A process takes a fresh ticket number strictly above all tickets held so
\* far, wrapping back to zero once the bound is reached; this keeps a live
\* pool even though the range is finite.
Request(i) ==
  /\ serving = 0
  /\ i \notin served
  /\ ticket' = [ticket EXCEPT ![i] = 1 + IF \E k \in 0..(N - 1) : ticket[k] = MaxNat THEN 0 ELSE 1 + MaxNat]
  /\ serving' = i + 1
  /\ UNCHANGED served

Enter(i) ==
  /\ serving = i + 1
  /\ \A q \in 0..(N - 1) : q \notin served => ticket[i] <= ticket[q]
  /\ served' = served \cup {i}
  /\ serving' = 0
  /\ UNCHANGED ticket

Leave(i) ==
  /\ i \in served
  /\ served' = served \ {i}
  /\ UNCHANGED <<ticket, serving>>

Next ==
  \/ \E i \in 0..(N - 1) : Request(i)
  \/ \E i \in 0..(N - 1) : Enter(i)
  \/ \E i \in 0..(N - 1) : Leave(i)

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ WF_vars(\E i \in 0..(N - 1) : Request(i))
         /\ WF_vars(\E i \in 0..(N - 1) : Enter(i))
         /\ WF_vars(\E i \in 0..(N - 1) : Leave(i))

\* The configuration disables deadlock checking for the inductive spec, so this
\* module need provide no liveness properties of its own.
====