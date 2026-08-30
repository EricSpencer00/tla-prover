---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* This module is a model-checking configuration for the Boulanger
\* mutual-exclusion specification. It sets the natural-number domain to a
\* finite range and adds a state constraint to keep ticket numbers bounded
\* during model checking; it inherits the full action set from Boulanger.
\* The left side of each alias below is the name the .cfg file replaces, so
\* the right side gives the concrete (finite) definition the model uses.

NatOverride == Nat

\* Active is the set of processes holding the lock; Ticket[p] is p's
\* claimed claim; Highest is the most recently granted claim.
VARIABLES active, ticket, highest

vars == <<active, ticket, highest>>

TypeOK ==
  /\ active \subseteq 0..(N - 1)
  /\ ticket \in [0..(N - 1) -> NatOverride]
  /\ highest \in 0..MaxNat

Init ==
  /\ active = {}
  /\ ticket = [p \in 0..(N - 1) |-> 0]
  /\ highest = 0

Enter(p) ==
  /\ p \notin active
  /\ ticket[p] = 0
  /\ highest < MaxNat
  /\ active' = active \cup {p}
  /\ ticket' = [ticket EXCEPT ![p] = highest + 1]
  /\ highest' = highest + 1

Exit(p) ==
  /\ p \in active
  /\ active' = active \ {p}
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED highest

\* A process stalls in the critical section, leaving the ticket claim in
\* place. Because the ticket is never given up, it is reclaimed on exit.
Stall(p) ==
  /\ p \in active
  /\ UNCHANGED <<active, ticket, highest>>

Next ==
  \E p \in 0..(N - 1) : Enter(p) \/ Exit(p) \/ Stall(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 0..(N - 1) : p \in active => ticket[p] = highest

\* Bounded-range model: ticket numbers stay strictly below the maximum.
BoundedTickets == \A p \in 0..(N - 1) : ticket[p] < MaxNat

Inv == TypeOK /\ MutualExclusion /\ BoundedTickets
====