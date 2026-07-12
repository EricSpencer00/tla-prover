---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
\* The natural numbers used by the algorithm are restricted to the finite
\* range 0..MaxNat.  This is the only place where the infinite set Nat is
\* overridden; all other uses of Nat in the imported Bakery module refer to
\* this finite set.
\* 
\* The constant Nat is defined in the .cfg file as the set {0, 1, ..., MaxNat}.
\* We keep the declaration here for clarity, but it is not used directly
\* in the specification (the imported Bakery module already uses Nat).
\* ----------------------------------------------------------------------
\* No additional type definitions are required because the Bakery module
\* already defines the necessary types for the algorithm.

\* ----------------------------------------------------------------------
\* State variables (inherited from Bakery)
\* ----------------------------------------------------------------------
VARIABLES Ticket, CS, Next

\* ----------------------------------------------------------------------
\* Initial state (same as Bakery, but with Nat restricted)
\* ----------------------------------------------------------------------
Init ==
    /\ Ticket = [i \in 1..N |-> 0]
    /\ CS = {}
    /\ Next = 0

\* ----------------------------------------------------------------------
\* Next-state relation (same as Bakery)
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in 1..N :
          /\ Ticket[i] = 0
          /\ Ticket' = [Ticket EXCEPT ![i] = Next]
          /\ Next' = (Next + 1) % (MaxNat + 1)
          /\ CS' = CS
    \/ \E i \in 1..N :
          /\ Ticket[i] # 0
          /\ \A j \in 1..N :
                (Ticket[j] # 0) => (Ticket[i] < Ticket[j] \/ (Ticket[i] = Ticket[j] /\ i < j))
          /\ CS' = CS \cup {i}
          /\ Ticket' = Ticket
          /\ Next' = Next
    \/ \E i \in 1..N :
          /\ i \in CS
          /\ CS' = CS \ {i}
          /\ Ticket' = Ticket
          /\ Next' = Next

\* ----------------------------------------------------------------------
\* Specification (inductive)
\* ----------------------------------------------------------------------
ISpec == Init /\ [][Next]_<<Ticket, CS, Next>>

\* ----------------------------------------------------------------------
\* Safety invariants (inherited from Bakery)
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in CS : i = j

TypeOK ==
    /\ Ticket \in [1..N -> Nat]
    /\ CS \subseteq 1..N
    /\ Next \in Nat

Inv ==
    \A i \in 1..N :
        /\ Ticket[i] = 0 \/ Ticket[i] \in Nat
    /\ CS \subseteq 1..N
    /\ Next \in Nat

\* ----------------------------------------------------------------------
\* The module does not define any liveness properties.
\* ----------------------------------------------------------------------
\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====