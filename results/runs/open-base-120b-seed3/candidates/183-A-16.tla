---- MODULE TLAPS ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

\* Backend pragmas (placeholders for TLAPS)
\* @zenon timeout 10
\* @isabelle timeout 10
\* @cvc3 timeout 10
\* @yices timeout 10
\* @verit timeout 10
\* @z3 timeout 10
\* @spass timeout 10
\* @ls4 timeout 10

VARIABLES dummy

Init == TRUE

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == {}

PROPERTIES == {}

\* Fundamental theorems

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV :
    \E x \in UNIV : x \notin S

====