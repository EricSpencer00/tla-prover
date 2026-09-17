----- MODULE imo_2019_p1 -----
EXTENDS Integers, TLAPS

THEOREM imo_2019_p1 ==
    \A f \in [Int -> Int] :
        (\A a, b \in Int : (f[2 * a] + 2 * f[b] = f[f[a + b]])) <=>
        (\A z \in Int : (f[z] = 0) \/ (\E c \in Int : \A z \in Int : f[z] = 2 * z + c))
BY SMT, SetExtensionality, NoSetContainsEverything
====
