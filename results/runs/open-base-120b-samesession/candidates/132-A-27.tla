---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS A, B, C, bound

(* distinct model values *)
ASSUME /\ A /= B /\ B /= C /\ A /= C
ASSUME bound \in Nat

ValueSet == { A, B, C }

(* finite sequence constructor limited by the bound *)
BoundedSeq(b) == { s \in Seq(ValueSet) : Len(s) <= b }

VARIABLES seq, pos, cand, cnt

vars == << seq, pos, cand, cnt >>

(* initial state *)
Init ==
   /\ seq \in BoundedSeq(bound)
   /\ pos = 1
   /\ cand \in ValueSet
   /\ cnt = 0

(* one step of the Boyer‑Moore scan *)
Next ==
   \/ /\ pos <= Len(seq)
      /\ LET x == seq[pos] IN
            IF cnt = 0 THEN
               /\ cand' = x
               /\ cnt'  = 1
            ELSE IF cand = x THEN
               /\ cand' = cand
               /\ cnt'  = cnt + 1
            ELSE
               /\ cand' = cand
               /\ cnt'  = cnt - 1
      /\ pos' = pos + 1
      /\ UNCHANGED seq
   \/ /\ pos > Len(seq)
      /\ UNCHANGED << seq, pos, cand, cnt >>

(* overall specification *)
Spec == Init /\ [] [Next]_vars

(* auxiliary counting function *)
Count(s, v) == Cardinality({ i \in DOMAIN s : s[i] = v })

(* type correctness invariant *)
TypeOK ==
   /\ seq \in BoundedSeq(bound)
   /\ pos \in Nat
   /\ cand \in ValueSet
   /\ cnt \in Nat

(* inductive invariant used for proof *)
Inv ==
   /\ cnt >= 0
   /\ pos \in 1..(Len(seq) + 1)

(* majority correctness property *)
Correct ==
   /\ pos > Len(seq) =>
        \A v \in ValueSet :
           (Count(seq, v) > Len(seq) / 2) => v = cand

====