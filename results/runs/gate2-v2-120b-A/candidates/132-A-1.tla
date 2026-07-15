---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

\*-----------------------------------------------------------------
-- Constants (will be given concrete values in the .cfg file)
-----------------------------------------------------------------*/
CONSTANTS A, B, C, bound, Seq

\*-----------------------------------------------------------------
-- Derived constant: the set of possible element values
-----------------------------------------------------------------*/
Values == {A, B, C}

\*-----------------------------------------------------------------
-- Helper definition: the set of all finite sequences (as functions) 
-- over Values whose length is at most the bound.
-----------------------------------------------------------------*/
SeqSet == { s \in [0..bound -> Values] : 
              \A i \in 0..bound : i # 0 => s[i] # InitVal } \cup
           {<<>>}  \* Include the empty sequence

\*-----------------------------------------------------------------
-- State variables
-----------------------------------------------------------------*/
VARIABLES seq, pos, cand, count

\*-----------------------------------------------------------------
-- Type correctness invariant (for debugging / TLC)
-----------------------------------------------------------------*/
TypeOK == /\ seq \in SeqSet
          /\ pos \in Nat
          /\ cand \in Values
          /\ count \in Nat

\*-----------------------------------------------------------------
-- Initial state
-----------------------------------------------------------------*/
Init ==
  /\ seq \in SeqSet
  /\ pos = 1
  /\ cand \in Values
  /\ count = 0

\*-----------------------------------------------------------------
-- The three cases of the Boyer‑Moore algorithm
-----------------------------------------------------------------*/
Next ==
  \/ /\ pos <= Len(seq)
     /\ LET x == seq[pos] IN
        /\ IF count = 0 THEN
              /\ cand' = x
              /\ count' = 1
           ELSE IF cand = x THEN
              /\ cand' = cand
              /\ count' = count + 1
           ELSE
              /\ cand' = cand
              /\ count' = count - 1
        /\ pos' = pos + 1
        /\ UNCHANGED seq
  \/ /\ pos > Len(seq) \* scanning finished, stay in a stutter state
     /\ UNCHANGED <<seq, pos, cand, count>>

\*-----------------------------------------------------------------
-- Specification
-----------------------------------------------------------------*/
Spec == Init /\ [][Next]_<<seq, pos, cand, count>>

\*-----------------------------------------------------------------
-- Safety invariant: any true majority element must equal the candidate
-----------------------------------------------------------------*/
Correct ==
  (pos > Len(seq)) => 
    \A v \in Values :
      (Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) / 2) => cand = v

\*-----------------------------------------------------------------
-- Inductive invariant (helps TLC) – the candidate is always a value
-- and the counter never exceeds the length scanned so far.
-----------------------------------------------------------------*/
Inv ==
  /\ cand \in Values
  /\ count \in Nat
  /\ count <= pos

\*-----------------------------------------------------------------
-- The set of invariants required by the .cfg file
-----------------------------------------------------------------*/
THEOREM TypeOKInv == Spec => []TypeOK
THEOREM CorrectInv == Spec => []Correct
THEOREM InvInv == Spec => []Inv

=============================================================================