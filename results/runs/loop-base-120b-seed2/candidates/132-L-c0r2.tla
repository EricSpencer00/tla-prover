---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

Values == {A, B, C}

Len(s) == IF DOMAIN s = {} THEN 0 ELSE Max(DOMAIN s)

(* Finite version of Seq, limited to length 0..bound *)
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

Init ==
    /\ seq \in BoundedSeq(Values)
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
          IF cnt = 0 THEN
              (cand' = x /\ cnt' = 1)
          ELSE IF x = cand THEN
              (cand' = cand /\ cnt' = cnt + 1)
          ELSE
              (cand' = cand /\ cnt' = cnt - 1)
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Scan

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ pos \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

Inv ==
    /\ cnt >= 0
    /\ (cnt = 0 => cand \in Values)

MajorityElement(e) == Cardinality({ i \in DOMAIN seq : seq[i] = e })

Correct ==
    /\ (pos > Len(seq))
       => (\A e \in Values :
               (MajorityElement(e) > Len(seq) / 2) => e = cand)

====