---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* sentinel value indicating undefined failure function entry
Sentinel == -1

\* State variables
VARIABLES str, n, fail, i, k, best, pc

\* Helper definitions
Idx(j) == j % n
CandIdx(j, offs, matchIdx) == (offs + matchIdx + 1) % n

Rot(s, off) == [j \in 0..n-1 |-> s[(off + j) % n]]

LexLe(s1, s2) ==
  \A j \in 0..n-1 :
    ( \A k \in 0..j-1 : s1[k] = s2[k] ) => s1[j] <= s2[j]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ n \in Nat \ {0}
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n-1 -> Int]
  /\ \A idx \in 0..2*n-1 : fail[idx] = Sentinel
  /\ i = Sentinel
  /\ k = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions corresponding to the algorithm steps
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF k < 2 * n THEN
        /\ pc' = "Lookup"
        /\ UNCHANGED <<str, n, fail, i, best>>
     ELSE
        /\ pc' = "Done"
        /\ UNCHANGED <<str, n, fail, i, k, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ i' = fail[Idx(k)]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, best, k>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ cur  == str[Idx(k)]
  /\ cand == str[CandIdx(k, best, i)]
  /\ IF cur = cand THEN
        /\ i' = i + 1
        /\ pc' = "InnerLoop"
        /\ UNCHANGED <<str, n, fail, best, k>>
     ELSE IF cur < cand THEN
        /\ best' = (k - i) % n
        /\ i'    = Sentinel
        /\ pc'   = "PostComp"
        /\ UNCHANGED <<str, n, fail, k>>
     ELSE
        /\ i' = Sentinel
        /\ pc' = "PostComp"
        /\ UNCHANGED <<str, n, fail, best, k>>

PostComp ==
  /\ pc = "PostComp"
  /\ idx == Idx(k)
  /\ fail' == [fail EXCEPT ![idx] = IF i = Sentinel THEN Sentinel ELSE i + 1]
  /\ k'   == k + 1
  /\ pc'  == "OuterCheck"
  /\ UNCHANGED <<str, n, best, i>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, i, k, best, pc>>

Next == OuterCheck \/ Lookup \/ InnerLoop \/ PostComp \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
vars == <<str, n, fail, i, k, best, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
TypeInvariant ==
  /\ n \in Nat \ {0}
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n-1 -> Int]
  /\ i \in Int
  /\ k \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..n-1 :
        LexLe(Rot(str, best), Rot(str, off))

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
SPECIFICATION == Spec
INVARIANTS == TypeInvariant, Correctness

\* The replacement operator required by the configuration.
\* It simply mirrors the constant CharacterSet (a finite subset of Nat).
\* No re‑definition of Nat is performed.
\* Note: this operator lives in the current module, matching the
\* "[ZSequences]CharacterSet" replacement used in the cfg.
CharacterSet == CharacterSet

====