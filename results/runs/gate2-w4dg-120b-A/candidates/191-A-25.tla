---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

Mod == 2 ^ D

VARIABLES tower
vars == <<tower>>

\* Bitwise AND: test whether the bits set in 'mask' are all set in 'val'.
\* Implemented arithmetically so the spec needs no Java override.
BitAnd(val, mask) ==
  LET f(i, acc) ==
        IF i = D THEN acc
        ELSE LET bit == 2 ^ i
                 acc2 == IF (val \div bit) % 2 = 1 /\ (mask \div bit) % 2 = 1
                            THEN acc + bit
                            ELSE acc
             IN f(i + 1, acc2)
  IN f(0, 0)

SmallestOn(t, k) == k < D /\ ((tower[t] \div (2 ^ k)) % 2 = 1)
                        /\ (tower[t] \div (2 ^ (k + 1))) * (2 ^ (k + 1)) = tower[t]

Init == tower = [i \in 0..(N - 1) |-> IF i = 0 THEN Mod - 1 ELSE 0]

Move ==
  \E k \in 0..(D - 1), src \in 0..(N - 1), dst \in 0..(N - 1) :
    /\ src # dst
    /\ BitAnd(tower[src], 2 ^ k) = 2 ^ k
    /\ SmallestOn(src, k)
    /\ ~(\E j \in 1..(k - 1) : BitAnd(tower[dst], 2 ^ j) = 2 ^ j)
    /\ tower' = [tower EXCEPT ![src] = @ - 2 ^ k, ![dst] = @ + 2 ^ k]

Next == Move

Spec == Init /\ [][Next]_vars

TypeOK == \A t \in 0..(N - 1) : tower[t] \in 0..(Mod - 1)

Inv == (tower[0] + tower[1] + tower[2] = Mod - 1)
        /\ tower[0] <= Mod - 1 /\ tower[1] <= Mod - 1 /\ tower[2] <= Mod - 1

====