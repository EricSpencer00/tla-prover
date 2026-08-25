---- MODULE MCMajority ----
EXTENDS Naturals, Reals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\*--- Elements and bounded sequences ---------------------------------
Elem == {A, B, C}

BoundedSeq == { s \in Seq(Elem) : Len(s) <= bound }

\*--- State variables -------------------------------------------------
VARIABLES seq, i, cand, cnt

\*--- Helper definitions -----------------------------------------------
Count(s, v) == Cardinality({ j \in DOMAIN s : s[j] = v })

MajoritySet(s) == { v \in Elem : Count(s, v) > Len(s) / 2 }

\*--- Initialization --------------------------------------------------
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cnt = 0
    /\ cand \in Elem

\*--- Main scanning step -----------------------------------------------
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt'  = 1
          ELSE IF x = cand THEN
              /\ cand' = cand
              /\ cnt'  = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt'  = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

\*--- Stuttering when scan is finished ---------------------------------
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next ==
    Scan \/ Done

\*--- Specification ----------------------------------------------------
vars == <<seq, i, cand, cnt>>

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Scan)

\*--- Invariants -------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Elem
    /\ cnt \in Nat

Correct ==
    /\ i > Len(seq)
    /\ \A v \in Elem :
          (Count(seq, v) > Len(seq) / 2) => v = cand

Inv ==
    LET M == MajoritySet(seq) IN
        (M = {} ) \/ (cnt = 0) \/ (cand \in M)

====