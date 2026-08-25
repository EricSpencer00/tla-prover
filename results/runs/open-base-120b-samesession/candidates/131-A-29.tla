---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Value

(* Import the main majority‑vote specification *)
EXTENDS Majority

(* State variables are those of the main specification *)
VARIABLES cand, count, i, seq, n

(* Reuse the initialization and transition actions from the main spec *)
Init == Majority!Init
Next == Majority!Next

(* The full specification required by the .cfg file *)
Spec == Init /\ [][Next]_<<cand, count, i, seq, n>>

(* --------------------------------------------------------------------- *)
(*  Invariant: type correctness                                            *)
(* --------------------------------------------------------------------- *)
TypeOK ==
    /\ cand \in Value
    /\ count \in Nat
    /\ i \in Nat
    /\ seq \in Seq(Value)
    /\ n \in Nat

(* --------------------------------------------------------------------- *)
(*  Invariant: main correctness                                           *)
(*    After the whole sequence has been scanned, any value that occurs   *)
(*    in a strict majority of positions must equal the current candidate *)
(* --------------------------------------------------------------------- *)
Correct ==
    /\ i = Len(seq)                                   \* whole input processed
    /\ \A v \in Value :
          ( Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2 )
          => cand = v

(* --------------------------------------------------------------------- *)
(*  Combined invariant (convenient for model checking)                    *)
(* --------------------------------------------------------------------- *)
Inv == TypeOK /\ Correct

====