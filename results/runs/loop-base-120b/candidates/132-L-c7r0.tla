---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

(* BoundedSeq replaces Seq from Sequences *)
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

Init ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ i = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

LenSeq == Len(seq) \* length of the current sequence

Scan ==
  /\ i <= LenSeq
  /\ LET x == seq[i] IN
       /\ IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt' = 1
          ELSE IF cand = x THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
          ELSE
            /\ cand' = cand
            /\ cnt' = cnt - 1
          END IF
  /\ i' = i + 1
  /\ UNCHANGED seq

Done ==
  /\ i > LenSeq
  /\ UNCHANGED <<seq, cand, cnt>>

Next == Scan \/ Done

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* Type correctness invariant *)
TypeOK ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ i \in Nat
  /\ cand \in {A, B, C}
  /\ cnt \in Nat

(* Helper: count occurrences of v in s *)
Count(s, v) == Cardinality({j \in DOMAIN s : s[j] = v})

(* Inductive invariant *)
Inv ==
  LET prefDomain == 1..(i-1) IN
    /\ i >= 1
    /\ cnt =
        Cardinality({j \in prefDomain : seq[j] = cand}) -
        Cardinality({j \in prefDomain : seq[j] # cand})

(* Majority correctness property *)
Correct ==
  [] ( (i = LenSeq + 1) =>
        \A e \in {A, B, C} :
          (Count(seq, e) > LenSeq / 2) => cand = e )

====