---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound, Seq

VARIABLES s, i, x, c

vars == {s, i, x, c}

(* Type checking invariant *)
TypeOK ==
    /\ s \in Seq
    /\ i \in 1..Len(s)+1
    /\ x \in {A, B, C}
    /\ c \in Nat
    /\ bound \in Nat

(* Initialization *)
Init ==
    /\ s \in Seq
    /\ i = 1
    /\ c = 0
    /\ x \in {A, B, C}

(* Scan action *)
Scan ==
    /\ i <= Len(s)
    /\ s' = s
    /\ i' = i + 1
    /\ ( (c = 0 /\ x' = s[i] /\ c' = 1) \/
         (c > 0 /\ x = s[i] /\ x' = x /\ c' = c + 1) \/
         (c > 0 /\ x # s[i] /\ x' = x /\ c' = c - 1) )

(* Stutter action when scan is complete *)
Stutter ==
    /\ i > Len(s)
    /\ s' = s
    /\ i' = i
    /\ x' = x
    /\ c' = c

Next == Scan \/ Stutter

Spec == Init /\ [][Next]_vars

(* Helper: number of occurrences of e in the scanned prefix *)
CountPrefix(e) ==
    Len({ j \in 1..i-1 : s[j] = e })

(* Inductive invariant: any majority element in the scanned prefix is the candidate *)
Inv ==
    \A e \in {A, B, C} :
        (CountPrefix(e) > (i-1)/2) => e = x

(* Correctness invariant after full scan *)
Correct ==
    (i > Len(s)) => (\A e \in {A, B, C} :
                       (#(SELECT j \in 1..Len(s) : s[j] = e) > Len(s)/2) => e = x)

====