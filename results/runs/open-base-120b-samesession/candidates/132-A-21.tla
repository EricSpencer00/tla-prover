---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The set of possible element values *)
ValueSet == { A, B, C }

(* Bounded sequence operator – finite sequences over S whose length ≤ bound *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, i, cand, count

(* Helper: the prefix of the input sequence processed so far (positions 1 … i‑1) *)
Prefix(i) == [j \in 1..(i-1) |-> seq[j]]

(* Number of occurrences of element e in a (finite) sequence s *)
Count(s, e) == Cardinality({ j \in DOMAIN s : s[j] = e })

(* Initial state *)
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i = 1
    /\ cand \in ValueSet
    /\ count = 0

(* One step of the Boyer‑Moore scan when there are still elements left *)
NextScan ==
    /\ i <= Len(seq)
    /\ LET a == seq[i] IN
       IF count = 0 THEN
           /\ cand' = a
           /\ count' = 1
       ELSE IF a = cand THEN
           /\ cand' = cand
           /\ count' = count + 1
       ELSE
           /\ cand' = cand
           /\ count' = count - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

(* Stutter step after the scan is finished *)
NextStutter ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, count>>

(* Overall next‑state relation *)
Next == NextScan \/ NextStutter

vars == <<seq, i, cand, count>>

(* Full specification, including weak fairness for the scan step *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Type‑correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i \in Nat
    /\ cand \in ValueSet
    /\ count \in Int

(* Inductive invariant relating count to the processed prefix *)
Inv ==
    /\ i >= 1
    /\ i <= Len(seq) + 1
    /\ count = IF i = 1 THEN 0
               ELSE 2 * Count(Prefix(i), cand) - (i - 1)

(* Correctness: after the whole sequence has been scanned, any true majority element must equal the candidate *)
Correct ==
    (i > Len(seq)) => 
        \A e \in ValueSet :
            (Count(seq, e) > Len(seq) / 2) => e = cand

====