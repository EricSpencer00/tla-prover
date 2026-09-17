---- MODULE exercise_2000_a2 ----
EXTENDS TLAPS, Integers

THEOREM exercise_2000_a2 ==
  \A N \in Nat :
    \E n \in Nat :
      n > N /\
      (\E i \in [{0, 1, 2, 3, 4, 5} -> Nat]:
        ((n) = (i[0]) * (i[0]) + (i[1]) * (i[1]) /\
         (n + 1) = (i[2]) * (i[2]) + (i[3]) * (i[3]) /\
         (n + 2) = (i[4]) * (i[4]) + (i[5]) * (i[5])))BY SMT, NoSetContainsEverything
====
