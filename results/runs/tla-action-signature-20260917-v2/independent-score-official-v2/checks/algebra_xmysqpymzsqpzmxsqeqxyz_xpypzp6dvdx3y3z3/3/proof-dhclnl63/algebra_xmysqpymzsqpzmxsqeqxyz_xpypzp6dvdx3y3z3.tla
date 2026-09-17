---- MODULE algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3 ----
EXTENDS Integers, TLAPS

Divides(a, b) == \E k \in Int : b = a * k

THEOREM algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3 ==
    \A x, y, z \in Int : (x - y) * (x - y) + (y - z) * (y - z) + (z - x) * (z - x) = x * y * z => Divides(x + y + z + 6, x * x * x + y * y * y + z * z * z)BY DEF Divides
====
