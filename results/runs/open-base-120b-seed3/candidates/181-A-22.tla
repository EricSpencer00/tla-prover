---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of Nat for model checking
NatOverride == { n \in Nat : n <= MaxNat }

VARIABLE n

\* Evenness predicate using the (infinite) Nat set
Even(x) == \E k \in Nat : x = 2 * k

\* Initialization: start with the smallest natural number
Init == n = 0

\* Transition: increment n while staying inside the bounded range
Next == /\ n' \in NatOverride
        /\ n' = n + 1

\* The overall specification for TLC
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Required identifiers for the configuration module
INIT == Init
NEXT == Next
INVARIANTS == << n \in NatOverride >>
PROPERTIES == << \A m \in NatOverride : Even(2 * m) >>

====