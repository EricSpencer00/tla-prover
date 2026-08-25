---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of Nat for model checking
NatOverride == Nat \cap 0..MaxNat

VARIABLE x

\* Helper definition: a number is even iff it is twice some natural number
IsEven(m) == \E k \in NatOverride : m = 2 * k

\* The theorem we are checking: the double of any natural number is even
Theorem == \A n \in NatOverride : IsEven(2 * n)

\* Initial state: start at 0 (any element of NatOverride would work)
Init == /\ x \in NatOverride
        /\ x = 0

\* Next action: iterate through the bounded range to explore all values
Next == /\ x \in NatOverride
        /\ x' = (x + 1) % (MaxNat + 1)

\* Specification required by the .cfg
SPECIFICATION == Init /\ [][Next]_<<x>>

\* Invariants and properties required by the .cfg
INVARIANTS == Theorem
PROPERTIES == Theorem

\* Assume the theorem holds at the constant level (helps TLC)
ASSUME Theorem

====