---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (provided by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT Value

\* ----------------------------------------------------------------------
\* State variables (inherited from MajorityVote spec; redeclared for type
\* checking purposes)
\* ----------------------------------------------------------------------
VARIABLES seq, cand, cnt

\* ----------------------------------------------------------------------
\* Helper definitions (used only in the proof, not part of the spec)
\* ----------------------------------------------------------------------
Len(s) == Len(s)
OccCnt(v, s) == Len({ i \in 0..Len(s)-1 : s[i] = v })

\* ----------------------------------------------------------------------
\* Initial state (identical to the main specification)
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in Seq(0..Len(seq), Value)
    /\ cand \in Value \/ cand = NULL
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Next-state relation (identical to the main specification)
\* ----------------------------------------------------------------------
NEXT ==
    \/ \E i \in 0..Len(seq)-1 :
          /\ i < Len(seq)
          /\ IF i = 0 THEN
                /\ cand' = seq[0]
                /\ cnt' = 1
                /\ UNCHANGED seq
            ELSE
                /\ IF seq[i] = cand THEN
                       /\ cnt' = cnt + 1
                       /\ cand' = cand
                       /\ UNCHANGED seq
                   ELSE
                       /\ IF cnt = 0 THEN
                              /\ cand' = seq[i]
                              /\ cnt' = 1
                              /\ UNCHANGED seq
                          ELSE
                              /\ cnt' = cnt - 1
                              /\ UNCHANGED cand
                              /\ UNCHANGED seq)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][NEXT]_<<cand, cnt, seq>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in Seq(0..Len(seq), Value)
    /\ cand \in Value \/ cand = NULL
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Main correctness invariant (the only possible majority element equals cand)
\* ----------------------------------------------------------------------
Correct ==
    Len(seq) > 0 =>
        (\A v \in Value :
            (OccCnt(v, seq) > Len(seq) / 2) => (v = cand))

\* ----------------------------------------------------------------------
\* Combined invariant (used only for the proof)
\* ----------------------------------------------------------------------
Inv == TypeOK /\ Correct

\* ----------------------------------------------------------------------
\* Safety property declarations
\* ----------------------------------------------------------------------
SafetyProperties ==
    TypeOK /\ Correct

\* ----------------------------------------------------------------------
\* Theorem (used for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Correctness ==
    Spec => []Correct

====