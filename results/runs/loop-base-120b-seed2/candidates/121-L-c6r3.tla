---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, ZSequences

CONSTANT MaxLen

VARIABLES str, n, best

(* --- Helper definitions --- *)

Rotation(s, o) == 
    [i \in 0..(n-1) |-> s[(o + i) % n]]

LexLeq(rot1, rot2) == 
    \E k \in 0..n :
        (\A i \in 0..(k-1) : rot1[i] = rot2[i]) /\ 
        (k = n \/ rot1[k] <= rot2[k])

MinimalRotation(s) ==
    CHOOSE o \in 0..(n-1) :
        \A o2 \in 0..(n-1) : LexLeq(Rotation(s, o), Rotation(s, o2))

(* --- Initialization and transition --- *)

Init ==
    /\ n \in 1..MaxLen
    /\ str \in [0..(n-1) -> CharacterSet]
    /\ best = MinimalRotation(str)

Next ==
    UNCHANGED <<str, n, best>>

Spec == Init /\ [][Next]_<<str, n, best>>

(* --- Invariants --- *)

TypeInvariant ==
    /\ n \in Nat
    /\ str \in [0..(n-1) -> CharacterSet]
    /\ best \in 0..(n-1)

Correctness ==
    /\ best \in 0..(n-1)
    /\ \A o \in 0..(n-1) : LexLeq(Rotation(str, best), Rotation(str, o))

====