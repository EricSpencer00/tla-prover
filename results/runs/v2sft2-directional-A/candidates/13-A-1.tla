---- MODULE MCBakery ----
EXTENDS Bakery

CONSTANTS N, MaxNat, Nat

\* The set of all state variables (those defined in Bakery)
vars == {Ticket, Flag}

\* Inductive initial condition: any state that satisfies the invariant
Init == Inv

\* Specification that starts from any invariant state and follows Next forever
ISpec == Init /\ [][Next]_vars

INVARIANTS MutualExclusion, TypeOK, Inv

====