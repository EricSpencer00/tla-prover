---- MODULE DyadicRationals ----
EXTENDS Integers, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (none required by the .cfg, but we expose the identifiers)
\* ----------------------------------------------------------------------
CONSTANTS
    One,          \* dyadic rational representing the number 1
    Half,         \* dyadic rational representing the number 1/2
    Norm          \* recursive normalization operator

\* ----------------------------------------------------------------------
\* State variable: the current dyadic rational, represented as a record
\* with fields 'num' (numerator) and 'den' (denominator)
\* ----------------------------------------------------------------------
VARIABLES p

\* ----------------------------------------------------------------------
\* Helper definitions for readability
\* ----------------------------------------------------------------------
Num == p["num"]
Den == p["den"]

\* ----------------------------------------------------------------------
\* Initialization: start with the dyadic rational One = 1/1
\* ----------------------------------------------------------------------
Init ==
    /\ p = [num |-> 1, den |-> 1]
    /\ One = p
    /\ Half = [num |-> 1, den |-> 2]

\* ----------------------------------------------------------------------
\* Normalization operator: if both numerator and denominator are even,
\* divide them by 2; otherwise leave the record unchanged.
\* This definition is recursive via the "Norm" constant that denotes the
\* operator itself.
\* ----------------------------------------------------------------------
Norm(r) ==
    IF (r["num"] % 2 = 0) /\ (r["den"] % 2 = 0) THEN
        Norm([num |-> r["num"] \div 2, den |-> r["den"] \div 2])
    ELSE
        r

\* ----------------------------------------------------------------------
\* Actions
\*   HalfIt  : halve the rational (multiply denominator by 2) and then normalize
\*   Reduce  : apply normalization directly (no change to numerator or denominator)
\* The system nondeterministically chooses one of these actions each step.
\* ----------------------------------------------------------------------
HalfIt ==
    /\ p' = Norm([num |-> p["num"], den |-> p["den"] * 2])

Reduce ==
    /\ p' = Norm(p)

Next ==
    \/ HalfIt
    \/ Reduce

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_p

\* ----------------------------------------------------------------------
\* Invariant: the denominator is always a positive power of two
\* ----------------------------------------------------------------------
DenIsPowerOfTwo ==
    /\ Den > 0
    /\ \A i \in Nat : Den = 2^i

\* ----------------------------------------------------------------------
\* Property: the rational represented by (Num / Den) is always in the range
\* (0, 2] – this follows from the construction but is expressed as a safety
\* invariant for model checking.
\* ----------------------------------------------------------------------
ValueRange ==
    /\ (Num \div Den) \in {0, 1, 2}   \* integer division gives 0,1,2
    /\ (Num % Den) = 0                \* value is an exact dyadic rational

\* ----------------------------------------------------------------------
\* THEOREM (optional) to expose the specification name expected by TLC
\* ----------------------------------------------------------------------
THEOREM Spec == Spec

====