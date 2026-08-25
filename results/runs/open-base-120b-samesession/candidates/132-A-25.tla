---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Distinct model values
ASSUME A =/= B /\ A =/= C /\ B =/= C
\* bound is a natural number
ASSUME bound \in Nat

\* The set of possible element values
ValueSet == { A, B, C }

\* Finite sequences of length at most bound over ValueSet
BoundedSeq == { s \in Seq : Len(s) <= bound }

VARIABLES seq, pos, cand, cnt

\* The tuple of all state variables
vars == << seq, pos, cand, cnt >>

\* Type correctness invariant
TypeOK == 
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

\* Initial state: arbitrary bounded sequence, start scanning at 1,
\* nondeterministically chosen candidate, counter zero
Init == 
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* One step of the Boyer‑Moore scan
Next == 
    \/ /\ pos <= Len(seq)
       LET x == seq[pos] IN
         /\ \/ /\ cnt = 0
                /\ cand' = x
                /\ cnt'  = 1
            \/ /\ cnt # 0 /\ cand = x
                /\ cnt'  = cnt + 1
                /\ cand' = cand
            \/ /\ cnt # 0 /\ cand # x
                /\ cnt'  = cnt - 1
                /\ cand' = cand
         /\ pos' = pos + 1
         /\ UNCHANGED seq
    \/ /\ pos > Len(seq)
       /\ UNCHANGED <<seq, pos, cand, cnt>>

\* Specification: init and always‑next
Spec == Init /\ [][Next]_vars

\* Correctness: after a complete scan, any true majority element must equal the candidate
Correct == 
    (pos = Len(seq) + 1) => 
        \A a \in ValueSet :
            ( Cardinality( { i \in 1..Len(seq) : seq[i] = a } ) > Len(seq) / 2 )
            => cand = a

\* A simple inductive invariant (type safety plus non‑negative counter)
Inv == TypeOK /\ cnt >= 0

=============================================================================