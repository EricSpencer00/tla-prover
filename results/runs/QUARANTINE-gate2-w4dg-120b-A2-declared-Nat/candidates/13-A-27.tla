---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES cs, ticket, choosing, nextTicket

vars == <<cs, ticket, choosing, nextTicket>>

\* The inductive invariant is assumed to hold at all reachable states, so the
\* model starts from any type-correct allocation of tickets, not just the empty
\* one.
StateConstraint == /\ cs \subseteq (1..N)
                   /\ ticket \in [1..N -> Nat]
                   /\ choosing \in [1..N -> BOOLEAN]
                   /\ nextTicket \in Nat

TypeOK == /\ cs \subseteq (1..N)
          /\ ticket \in [1..N -> Nat]
          /\ choosing \in [1..N -> BOOLEAN]
          /\ nextTicket \in Nat

MutualExclusion == \A p1 \in cs, p2 \in cs : p1 = p2

\* Backward compatibility: the normal full invariant of the Bakery spec.
Inv == /\ TypeOK
        /\ MutualExclusion

\* Model checking overrides the infinite natural numbers with a finite range.
NatOverride == Nat

\* The inductive spec: any state satisfying StateConstraint can be the start.
ISpec == /\ StateConstraint
         /\ [][Next]_vars
         /\ WF_vars(Enter)
         /\ WF_vars(Exit)

Init == StateConstraint

BeginChoose(p) == /\ ~ choosing[p]
                  /\ ~ (p \in cs)
                  /\ choosing' = [choosing EXCEPT ![p] = TRUE]
                  /\ UNCHANGED <<cs, ticket, nextTicket>>

AssignTicket(p) == /\ choosing[p]
                   /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
                   /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
                   /\ choosing' = [choosing EXCEPT ![p] = FALSE]
                   /\ UNCHANGED cs

\* A process enters the critical section only after every lower ticket holder
\* has left, and only if its ticket is still below the maximum bound.
Enter(p) == /\ ~ choosing[p]
            /\ p \notin cs
            /\ ticket[p] < MaxNat
            /\ \A q \in 1..N : (q # p /\ ticket[q] < ticket[p]) => q \notin cs
            /\ cs' = cs \cup {p}
            /\ UNCHANGED <<ticket, choosing, nextTicket>>

Exit(p) == /\ p \in cs
           /\ cs' = cs \ {p}
           /\ UNCHANGED <<ticket, choosing, nextTicket>>

Next == \/ \E p \in 1..N : BeginChoose(p)
        \/ \E p \in 1..N : AssignTicket(p)
        \/ \E p \in 1..N : Enter(p)
        \/ \E p \in 1..N : Exit(p)

====