---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend-pragma operators for TLAPS. Each records a call to a backend prover
\* with its timeout, to be emitted during proof checking. No actor model at all.
\* The theorems are the two foundational set facts mentioned in the description.

CONSTANTS zenon, isabelle, cvc3, yices, veriT, z3, spass, ls4

\* Each backend call is a record naming the prover and the timeout; the spec does
\* not explore these, so they are fixed and harmless.
\* Theorems: set extensionality, and that no set is universal.
Init == [p \in 1..3 |-> [op |-> IF p = 1 THEN "zenonPri" ELSE IF p = 2 THEN "isabelleSec" ELSE "cvc3Tert", tm |-> IF p = 1 THEN 2 ELSE 3]]
Zenon1 == [p |-> "zenonPri", tm |-> 2]
IsabelleSec == [p |-> "isabelleSec", tm |-> 3]
Cvc3Tert == [p |-> "cvc3Tert", tm |-> 3]
Yices4 == [p |-> "yicesQuar", tm |-> 2]
VeriT5 == [p |-> "veriTQuin", tm |-> 2]
Z34 == [p |-> "z3Sen", tm |-> 2]
Spass6 == [p |-> "spassSept", tm |-> 2]
Ls4 == [p |-> "ls4Oc", tm |-> 2]

\* No real system state -- the spec is the empty action set over the priming
\* of Init (required by the template, never actually reachable).
InitSpec == Init
NextSpec == InitSpec

\* The two set-theoretic facts the description calls for.
Extensionality == \A s, t \in SUBSET Nat : (\A x \in Nat : x \in s <=> x \in t) => s = t
NoUniversalSet == \A s \in SUBSET Nat : \A x \in Nat : x \in s => FALSE

\* The spec consists of the priming of Init with nothing else.
Spec == InitSpec /\ [][NextSpec]_InitSpec

\* The theorems count as the module's invariants.
Invariants == Extensionality /\ NoUniversalSet

\* Expected output: there are no liveness properties to check.
Properties == TRUE

====