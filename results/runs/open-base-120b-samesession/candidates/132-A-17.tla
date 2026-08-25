---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS A, B, C, bound

(* The set of possible element values *)
Values == { A, B, C }

(* A finite version of Seq, limited by the bound parameter *)
BoundedSeq == { s \in Seq(Values) : Len(s) <= bound }

VARIABLES seq, pos, cand, cnt

vars == << seq, pos, cand, cnt >>

(* Initial state: a bounded sequence, scan starts at 1, counter 0,
   candidate chosen nondeterministically from the value set *)
Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cnt = 0
    /\ cand \in Values

(* Helper to count occurrences of a value in a sequence *)
Count(s, v) ==
    Cardinality({ i \in 1..Len(s) : s[i] = v })

(* Scan the next element according to the Boyer‑Moore rules *)
Scan ==
    /\ pos <= Len(seq)
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

(* No further action once the whole sequence has been scanned *)
Done ==
    /\ pos > Len(seq)
    /\ UNCHANGED << seq, cand, cnt >>

Next ==
    Scan \/ Done

(* The specification to be checked *)
Spec ==
    Init /\ [][Next]_vars

(* Type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cnt \in Nat
    /\ cand \in Values
    /\ pos <= Len(seq) + 1

(* Majority‑correctness property: any true majority element equals the
   final candidate after the scan is complete *)
Correct ==
    /\ pos > Len(seq)
    => \A v \in Values :
          (Count(seq, v) > Len(seq) / 2) => v = cand

(* Simple inductive invariant *)
Inv ==
    /\ cnt >= 0
    /\ pos >= 1
    /\ pos <= Len(seq) + 1

====