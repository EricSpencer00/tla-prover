---- MODULE exercise_18_4 ----
EXTENDS Integers, TLAPS

Cube(x) == x * x * x

THEOREM exercise_18_4 ==
    \A n \in Nat :
        (\E x, y, z, w \in Int :
            Cube(x) + Cube(y) = n /\
            Cube(z) + Cube(w) = n /\
            x # z /\ x # w /\ y # z /\ y # w)
        => n >= 1729BY DEF Cube
====
