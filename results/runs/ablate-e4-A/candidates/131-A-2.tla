---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value, SEQ

VARIABLES candidate, count, pos

UNDEF == "UNDEF"

(* Helper: Count the occurrences of a value in SEQ *)
Count(v) == Len({ i \in 1..Len(SEQ) : SEQ[i] = v })

(* Initial state: no candidate, zero count, start at position 1 *)
Init == /\ candidate = UNDEF
        /\ count = 0
        /\ pos = 1

(* Scanning step: processes the current element if any remain *)
Scan ==
    /\ pos <= Len(SEQ)
    /\ IF count = 0 THEN
          /\ candidate' = SEQ[pos]
          /\ count' = 1
          /\ pos' = pos + 1
       ELSE IF SEQ[pos] = candidate THEN
          /\ candidate' = candidate
          /\ count' = count + 1
          /\ pos' = pos + 1
       ELSE
          /\ candidate' = candidate
          /\ count' = count - 1
          /\ pos' = pos + 1

(* Done step: no further action after all elements processed *)
ScanDone ==
    /\ pos > Len(SEQ)
    /\ UNCHANGED <<candidate, count, pos>>

Next == Scan \/ ScanDone

Spec == Init /\ [][Next]_<<candidate, count, pos>>

TypeOK ==
    /\ pos \in 1..Len(SEQ)+1
    /\ count \in Nat
    /\ candidate \in Value \/ {UNDEF}

Correct ==
    /\ pos > Len(SEQ)
    /\ \A v \in Value : Count(v) > Len(SEQ)/2 => candidate = v

Inv == Correct

====