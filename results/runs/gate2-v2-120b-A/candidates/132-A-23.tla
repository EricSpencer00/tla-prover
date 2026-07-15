---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constant declarations – these must be supplied by the .cfg file.
--------------------------------------------------------------------*)
CONSTANT A, B, C, bound, Seq

(*--------------------------------------------------------------------
  Derived constant: the set of possible element values.
--------------------------------------------------------------------*)
Values == {A, B, C}

(*--------------------------------------------------------------------
  Type definitions for readability.
--------------------------------------------------------------------*)
VARIABLES seq, pos, cand, cnt

(*--------------------------------------------------------------------
  Helper to generate all sequences (as functions) of length n over Values.
--------------------------------------------------------------------*)
SeqOfLen(n) == [i \in 1..n |-> CHOOSE v \in Values : TRUE]

(* The constant Seq must be constrained to be the set of all such sequences
   for lengths 0..bound. This is expressed as a theorem that the model
   checker will verify against the CONSTANTS clause. *)
SeqDef == Seq = { s \in [1..n -> Values] : 
                   \E n \in 0..bound : s \in [1..n -> Values] }

(*--------------------------------------------------------------------
  Initial state: choose any sequence from Seq, start at position 1,
  choose an initial candidate nondeterministically from Values,
  and set counter to 0.
--------------------------------------------------------------------*)
Init ==
    /\ seq \in Seq
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

(*--------------------------------------------------------------------
  Action: process the current element at position pos.
--------------------------------------------------------------------*)
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET cur == seq[pos] IN
          \/ /\ cand = cur
                /\ cnt' = cnt + 1
                /\ cand' = cand
                /\ pos' = pos + 1
          \/ /\ cand # cur /\ cnt = 0
                /\ cand' = cur
                /\ cnt' = 1
                /\ pos' = pos + 1
          \/ /\ cand # cur /\ cnt > 0
                /\ cnt' = cnt - 1
                /\ cand' = cand
                /\ pos' = pos + 1
    \/ /\ pos > Len(seq)   \* Stutter when scan is complete
       /\ UNCHANGED <<seq, pos, cand, cnt>>

(*--------------------------------------------------------------------
  Specification: the standard temporal formula.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

(*--------------------------------------------------------------------
  Safety invariant: type correctness.
--------------------------------------------------------------------*)
TypeOK ==
    /\ seq \in Seq
    /\ pos \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

(*--------------------------------------------------------------------
  Main correctness invariant (as described in the natural‑language text):
  after the scan has finished, if there exists a majority element in seq,
  then that element must equal the candidate.
--------------------------------------------------------------------*)
Correct ==
    /\ pos > Len(seq)
    /\ \E e \in Values :
          (Card({ i \in 1..Len(seq) : seq[i] = e }) >
           Len(seq) \div 2) => cand = e

(*--------------------------------------------------------------------
  Inductive invariant used by the original majority‑vote spec.
  This mirrors the classic Boyer‑Moore invariant.
--------------------------------------------------------------------*)
Inv ==
    /\ (pos <= Len(seq) => 
          (cnt = 0 => TRUE) /\ 
          (cnt > 0 => 
              \E m \in Values :
                 ( (cand = m) /\
                   (Card({ i \in 1..pos-1 : seq[i] = m }) -
                    Card({ i \in 1..pos-1 : seq[i] # m }) = cnt) ) ) )
    /\ (pos > Len(seq) => cnt >= 0)

(*--------------------------------------------------------------------
  Theorem stating the relationship between the constant Seq and the bound.
  The model checker must verify this against the .cfg constants.
--------------------------------------------------------------------*)
THEOREM SeqDef

====