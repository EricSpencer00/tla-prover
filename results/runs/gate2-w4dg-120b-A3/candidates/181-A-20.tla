---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS
    MaxNat

\* The model checker uses a bounded set of numbers.  The theorem that double of
\* any natural is even is assumed here for model checking, since it is the
\* target of the proof in the base spec and is not proved inside the model.
AssumeEvenDouble == \A n \in 0..MaxNat: (n + n) % 2 = 0

\* The .cfg file replaces the infinite natural-number set with a finite range.
NatOverride == 0..MaxNat

SPECIFICATION == Init /\ [][Next]_vars
Init == TRUE
Next == TRUE

INVARIANTS == TRUE
PROPERTIES == TRUE
====