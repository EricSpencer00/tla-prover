---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, TLC, Majority

CONSTANT Value

VARIABLES Cand, Count, Arr, i

(*-- Initialization and next-state relation inherited from the main specification --*)
Init == Majority.Init
Next == Majority.Next
Spec == Init /\ [][Next]_<<Cand, Count, Arr, i>>

(*-- Safety invariants --*)
TypeOK == Cand \in Value \/ Cand = "None" 
           /\ Count \in Nat 
           /\ Arr \in [1..Len(Arr) -> Value] 
           /\ i \in 0..Len(Arr)

Correct == \A e \in Value : 
            (Card({j : j \in 1..Len(Arr) : Arr[j] = e}) > Len(Arr)/2) => Cand = e

Inv == Correct

====