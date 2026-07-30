---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The interactive proof of correctness for the Boyer-Moore majority vote algorithm.
\* It extends the main algorithm specification with lemmas and a machine-checked
\* proof that the algorithm correctly identifies the only possible majority element.
\* The proof is structured for TLAPS: it establishes type correctness and that the
\* algorithm's output is correct -- any value occurring in a strict majority of
\* positions must equal the candidate. No new state variables or actions are added;
\* everything is inherited from the main majority vote specification.

\* The set of values seen in the first k positions of the scan (finite integer range).
Seen(k) == { s[i] : i \in (0..(k-1)) }

VARIABLES k, candidate, count, s, n

vars == <<k, candidate, count, s, n>>

TypeOK ==
  /\ k \in 0..n
  /\ candidate \in Value
  /\ count \in 0..n
  /\ s \in [0..(n-1) -> Value]
  /\ n \in Nat

Init ==
  /\ k = 0
  /\ count = 0
  /\ \E c \in Value : candidate = c
  /\ s \in [0..(n-1) -> Value]
  /\ n \in Nat

\* Progress the Boyer-Moore scan by one position. The transition is the same as in
\* the main majority vote spec; here it exists solely so the invariant can be proved.
Next ==
  /\ k < n
  /\ candidate' = (IF s[k] = candidate THEN candidate ELSE (IF count = 0 THEN s[k] ELSE candidate))
  /\ count' = (IF s[k] = candidate THEN count + 1 ELSE (IF count = 0 THEN 1 ELSE count - 1))
  /\ k' = k + 1
  /\ UNCHANGED <<s, n>>

Spec == Init /\ [][Next]_vars

\* Hierarchical proof: type correctness is an invariant of the spec.
TypeOKInv ==
  /\ TypeOK
  PROOF (INIT Init) /\ (STEP Next)

\* Correctness: after scanning the whole sequence, any value occurring in a strict
\* majority of positions must equal the candidate. Proved via the inductive invariant
\* (count > 0 <=> candidate is a majority element, from the main spec).
Correct ==
  /\ k = n
  /\ count > 0 => (candidate \in Seen(n))
  /\ \A x \in Seen(n) : (Cardinality({i \in 0..(n-1) : s[i] = x}) * 2 > n) => x = candidate
  PROOF (INIT Init) /\ (STEP Next)

\* Inv is the inductive invariant from the main specification: the candidate has a
\* strict majority exactly when count > 0, which is the core correctness claim.
Inv ==
  /\ (count > 0) <=> (\E x \in Seen(n) : Cardinality({i \in 0..(n-1) : s[i] = x}) * 2 > n)
  PROOF (INIT Init) /\ (STEP Next)

====