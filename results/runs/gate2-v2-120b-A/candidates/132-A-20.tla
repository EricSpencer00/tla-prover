---------------------------- MODULE MCMajority ----------------------------
EXTENDS Naturals, FiniteSets

(*--------------------------------------------------------------------
  Constants required by the .cfg file
--------------------------------------------------------------------*)
CONSTANTS A, B, C, bound, Seq

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
ValueSet == {A, B, C}

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES seq, pos, cand, cnt

(*--------------------------------------------------------------------
  State predicate: seq must be a function from 1..Len(seq) to ValueSet,
  and the length must be between 0 and bound (inclusive).  For the
  empty sequence we use a function with domain 0 (i.e., the empty set).
--------------------------------------------------------------------*)
SeqLen(seq) == 
  IF seq = [i \in {} -> {}] THEN 0 
  ELSE Len({i \in DOMAIN seq : TRUE})

SeqOk(seq) == 
  /\ \E n \in 0..bound : 
        /\ seq \in [1..n -> ValueSet] 
        /\ (n = 0 => seq = [i \in {} -> {}])
  /\ SeqLen(seq) <= bound

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init == 
  /\ \E n \in 0..bound : 
        /\ seq \in [1..n -> ValueSet]
        /\ (n = 0 => seq = [i \in {} -> {}])
  /\ pos = 1
  /\ cand \in ValueSet
  /\ cnt = 0
  /\ SeqOk(seq)

(*--------------------------------------------------------------------
  Helper to get the current element (if any)
--------------------------------------------------------------------*)
Cur(seq, p) == 
  IF p \in DOMAIN seq THEN seq[p] ELSE NONE

(*--------------------------------------------------------------------
  Transition relation (NEXT) – the Boyer‑Moore scan step
--------------------------------------------------------------------*)
Next == 
  \/ /\ pos <= SeqLen(seq)
        /\ LET x == Cur(seq, pos) IN
           CASE 
             cnt = 0 -> 
               /\ cand' = x
               /\ cnt'  = 1
               /\ pos'  = pos + 1
           [] cnt # 0 /\ cand = x -> 
               /\ cand' = cand
               /\ cnt'  = cnt + 1
               /\ pos'  = pos + 1
           [] cnt # 0 /\ cand # x -> 
               /\ cand' = cand
               /\ cnt'  = cnt - 1
               /\ pos'  = pos + 1
        /\ UNCHANGED seq
  \/ /\ pos > SeqLen(seq) 
        /\ UNCHANGED <<seq, pos, cand, cnt>>
  \/ /\ \E n \in 0..bound :
        /\ seq' \in [1..n -> ValueSet] 
        /\ (n = 0 => seq' = [i \in {} -> {}])
        /\ pos' = 1
        /\ cand' \in ValueSet
        /\ cnt' = 0
        /\ SeqOk(seq')
        /\ UNCHANGED <<seq, pos, cand, cnt>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK == 
  /\ SeqOk(seq)
  /\ pos \in Nat
  /\ cand \in ValueSet
  /\ cnt \in Nat

(*--------------------------------------------------------------------
  Correctness invariant (safety property)
  If a value occurs more than half the length of the sequence, then
  after the scan is finished (pos > Len(seq)) that value must equal cand.
--------------------------------------------------------------------*)
Correct ==
  /\ (pos > SeqLen(seq) /\ SeqLen(seq) > 0) => 
       \A v \in ValueSet :
         ( Cardinality({i \in DOMAIN seq : seq[i] = v}) > SeqLen(seq) / 2 )
         => v = cand

(*--------------------------------------------------------------------
  Inductive invariant (same as Correct in this setting, but kept separate)
--------------------------------------------------------------------*)
Inv == Correct

(*--------------------------------------------------------------------
  Theorem (optional, for TLC)
--------------------------------------------------------------------*)
THEOREM Spec => []Inv

=============================================================================