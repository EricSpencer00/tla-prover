---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

VARIABLES p, q

\* ----------------------------------------------------------------------
\* Record definition for a dyadic rational
\* ----------------------------------------------------------------------
DRec == [num : Int, den : Nat]

\* ----------------------------------------------------------------------
\* Initial state: the dyadic rational ONE = 1/1
\* ----------------------------------------------------------------------
Init ==
    /\ p = [num |-> 1, den |-> 1]
    /\ q = [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Halving operator: multiplies the denominator by 2, leaving the numerator unchanged
\* ----------------------------------------------------------------------
Half(p) ==
    [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* Normalization operator (recursive description in comments)
\* The actual initialization sets p to its normal form; the operator is not
\* invoked during steps because the specification does not require explicit
\* recursion – the behaviour is captured by the INIT and NEXT actions.
\* ----------------------------------------------------------------------
Norm(p) ==
    IF /\ p.num % 2 = 0
       /\ p.den % 2 = 0
    THEN [num |-> p.num \div 2, den |-> p.den \div 2]
    ELSE p

\* ----------------------------------------------------------------------
\* Next-state relation: at each step the system may either halve the current
\* dyadic rational, or normalize it (if both components are even).  The variable
\* q mirrors the current value of p and is used only to expose an additional
\* observable state component.
\* ----------------------------------------------------------------------
Next ==
    \/ /\ p' = Half(p)
       /\ q' = p'
    \/ /\ p' = Norm(p)
       /\ q' = p'

\* ----------------------------------------------------------------------
\* Specification: standard temporal formula
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<p, q>>

\* ----------------------------------------------------------------------
\* Invariant: both numerator and denominator stay non‑negative; the denominator
\* is never zero.
\* ----------------------------------------------------------------------
Positivity ==
    /\ p.num >= 0
    /\ p.den > 0

\* ----------------------------------------------------------------------
\* Optional safety property: the value represented by (p.num / p.den) never
\* exceeds 2 (this is merely illustrative; it is not required by the cfg).
\* ----------------------------------------------------------------------
Bounded ==
    p.num <= 2 * p.den

=============================================================================