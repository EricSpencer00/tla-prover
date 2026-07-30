---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* Variable set is inherited from the Bakery specification.
VARIABLES vars

vars == [cs : SUBSET (1..N), ticket : [1..N -> Nat], choosing : SUBSET (1..N)]

TypeOK ==
  /\ vars.cs \subseteq (1..N)
  /\ vars.ticking \in [1..N -> Nat]
  /\ vars.choosing \subseteq (1..N)

\* The inductive specification starts from any type-correct state, not just the
\* empty-critical-section state.
Init ==
  /\ vars.cs = {}
  /\ vars.ticket = [p \in 1..N |-> 0]
  /\ vars.choosing = {}

\* A process begins choosing a ticket.
Choose(p) ==
  /\ p \notin vars.cs
  /\ p \notin vars.choosing
  /\ vars' = [vars EXCEPT !.choosing = vars.choosing \cup {p}]
  /\ UNCHANGED <<>>


\* Assign the next ticket, bounded by MaxNat.
Assign(p) ==
  /\ p \in vars.choosing
  /\ vars.ticket' = [vars.ticket EXCEPT ![p] = IF Vars.ticket[p] < MaxNat THEN vars.ticket[p] + 1 ELSE MaxNat]
  /\ vars.choosing' = vars.choosing \ {p}
  /\ UNCHANGED <<>>


\* Enter the critical section once no one with a strictly lower ticket is inside.
Enter(p) ==
  /\ p \notin vars.cs
  /\ p \notin vars.choosing
  /\ \A q \in vars.cs : vars.ticket[p] <= vars.ticket[q]
  /\ vars.cs' = vars.cs \cup {p}
  /\ UNCHANGED <<vars.ticket, vars.choosing>>

\* Exit the critical section and reset the ticket.
Exit(p) ==
  /\ p \in vars.cs
  /\ vars.cs' = vars.cs \ {p}
  /\ vars.ticket' = [vars.ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<vars.choosing>>

Next ==
  \/ \E p \in 1..N : Choose(p) \/ Assign(p) \/ Enter(p) \/ Exit(p)

\* Mutual exclusion: the critical sections of any two distinct processes are
\* disjoint, so at most one process is ever inside.
MutualExclusion == \A a, b \in vars.cs : a = b

\* The full invariant maintained by the algorithm.
Inv == /\ MutualExclusion /\ TypeOK

ISpec == Init /\ [][Next]_vars

====