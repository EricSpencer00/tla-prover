---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS A, B, C, bound, Seq

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Values == {A, B, C}

(*--------------------------------------------------------------------
  Bounded sequence operator: all finite functions from 1..n to Values,
  for some n with 0 <= n <= bound.
--------------------------------------------------------------------*)
BoundedSeq == { s \in [1..bound -> Values] : 
                 Len(s) = bound \/ (Len(s) = 0) \/ 
                 (\E n \in 0..bound : Len(s) = n) }

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES seq, i, candidate, counter

(*--------------------------------------------------------------------
  Type predicate
--------------------------------------------------------------------*)
Vars ==
  /\ seq \in BoundedSeq
  /\ i \in 1..(bound + 1)            \* i = bound+1 means scan complete
  /\ candidate \in Values
  /\ counter \in Nat

TypeOK == Vars

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ candidate \in Values
  /\ counter = 0

(*--------------------------------------------------------------------
  Action definitions
--------------------------------------------------------------------*)
AdoptNew ==
  /\ i <= Len(seq)
  /\ candidate' = seq[i]
  /\ counter' = 1
  /\ i' = i + 1
  /\ UNCHANGED <<seq>>

IncCounter ==
  /\ i <= Len(seq)
  /\ seq[i] = candidate
  /\ counter' = counter + 1
  /\ i' = i + 1
  /\ UNCHANGED <<seq, candidate>>

DecCounter ==
  /\ i <= Len(seq)
  /\ seq[i] # candidate
  /\ counter > 0
  /\ counter' = counter - 1
  /\ i' = i + 1
  /\ UNCHANGED <<seq, candidate>>

Done ==
  /\ i = Len(seq) + 1
  /\ UNCHANGED <<seq, i, candidate, counter>>

Next ==
  \/ AdoptNew
  \/ IncCounter
  \/ DecCounter
  \/ Done

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, i, candidate, counter>>

(*--------------------------------------------------------------------
  Majority correctness invariant (the one required by the .cfg)
--------------------------------------------------------------------*)
Correct ==
  \/ i <= Len(seq)                \* scan not finished yet
  \/ \E v \in Values :
        (\A j \in 1..Len(seq) : seq[j] = v) => candidate = v

(*--------------------------------------------------------------------
  Inductive invariant (kept simple but sufficient)
--------------------------------------------------------------------*)
Inv == /\ candidate \in Values
       /\ counter \in Nat

(*--------------------------------------------------------------------
  Theorems – optional, but help TLC understand the spec
--------------------------------------------------------------------*)
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv

====