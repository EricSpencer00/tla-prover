---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT Value

(*--------------------------------------------------------------------
  Type definitions
--------------------------------------------------------------------*)
Vals == Value

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES seq, pos, cand, cnt

(*--------------------------------------------------------------------
  Type correctness invariant (for readability)
--------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq(Vals)
  /\ pos \in Nat
  /\ cand \in Vals
  /\ cnt \in Nat

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Seq(V) == SeqFromTo(1, LenSeq) \ {<<>>} \cup {<<>>} (* placeholder to allow any finite sequence *)
SeqFromTo(i, j) == CHOOSE s \in Seq(Vals) : Len(s) = j - i + 1

LenSeq == Len(seq)

Occurrences(v, s) == { i \in 1..Len(s) : s[i] = v }

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ seq \in Seq(Vals)
  /\ pos = 1
  /\ cand = seq[1]
  /\ cnt = 1

(*--------------------------------------------------------------------
  Next-state relation (Boyer‑Moore majority vote algorithm)
--------------------------------------------------------------------*)
Next ==
  \/ /\ pos < Len(seq)
     /\ pos' = pos + 1
     /\ IF cnt = 0
        THEN /\ cand' = seq[pos']
             /\ cnt' = 1
        ELSE IF seq[pos'] = cand
             THEN /\ cand' = cand
                  /\ cnt' = cnt + 1
             ELSE /\ cand' = cand
                  /\ cnt' = cnt - 1
     /\ UNCHANGED <<seq>>
  \/ /\ pos = Len(seq)
     /\ UNCHANGED <<seq, pos, cand, cnt>>

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

(*--------------------------------------------------------------------
  Inductive invariant from the main specification (simplified)
--------------------------------------------------------------------*)
Inv ==
  /\ CandIsCandidate ==
       \E n \in 1..pos :
         /\ cand = seq[n]
         /\ (cnt = Cardinality({ k \in 1..pos : seq[k] = cand })
             - Cardinality({ k \in 1..pos : seq[k] # cand }))
  /\ CandidateMayBeMajority :=
       (cnt > 0) => (cand \in Vals)

(*--------------------------------------------------------------------
  Correctness property
--------------------------------------------------------------------*)
Correct ==
  /\ pos = Len(seq)
  /\ \A v \in Vals :
        (Cardinality(Occurrences(v, seq)) > Len(seq) / 2) =>
          v = cand

(*--------------------------------------------------------------------
  Theorem (for TLAPS) that the invariant holds for the specification
--------------------------------------------------------------------*)
THEOREM InvIsInvariant ==
  Spec => []Inv

====