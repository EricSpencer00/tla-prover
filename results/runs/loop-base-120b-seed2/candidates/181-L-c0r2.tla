---- MODULE MC_sums_even ----
EXTENDS Naturals

\*--------------------------------------------------------------------
\* Configuration constants
\*--------------------------------------------------------------------
CONSTANT MaxNat

\* Provide a default value for MaxNat so the model can be checked
\* even if the .cfg file does not assign it.  The value is large enough
\* for the intended bound (0..1_000_000).
MaxNat == 1000000

\*--------------------------------------------------------------------
\* Finite version of the natural numbers for model checking
\*--------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\*--------------------------------------------------------------------
\* State variable
\*--------------------------------------------------------------------
VARIABLE n

\*--------------------------------------------------------------------
\* Initial state predicate
\*--------------------------------------------------------------------
Init == n = 0

\*--------------------------------------------------------------------
\* Next‑state relation: increment while staying inside the finite range
\*--------------------------------------------------------------------
Next == 
    /\ n \in NatOverride
    /\ n' = n + 1
    /\ n' \in NatOverride

\*--------------------------------------------------------------------
\* Full specification (trivial safety property)
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<n>>

\*--------------------------------------------------------------------
\* The theorem we are checking: the double of any natural is even
\*--------------------------------------------------------------------
Theorem == \A m \in NatOverride : (2 * m) % 2 = 0

\*--------------------------------------------------------------------
\* Assume the theorem holds at the constant level (enables TLC checking)
\*--------------------------------------------------------------------
ASSUME Theorem

\*--------------------------------------------------------------------
\* Required identifiers for the configuration file
\*--------------------------------------------------------------------
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == Theorem
PROPERTIES == Theorem
====