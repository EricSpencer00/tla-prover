---- MODULE imo_1981_p6 ----
EXTENDS TLAPS, Integers

THEOREM imo_1981_p6 ==
    \A f \in [Nat -> [Nat -> Nat]] :
        (\A y \in Nat : (f[0][y] = y + 1)) /\
        (\A x \in Nat : (f[x+1][0] = f[x][1])) /\
        (\A x, y \in Nat : (f[x+1][y+1] = f[x][f[x+1][y]]))
        => (\A y \in Nat : (f[4][y+1] = (f[4][y] + 3) - 3))
BY SMT
====
