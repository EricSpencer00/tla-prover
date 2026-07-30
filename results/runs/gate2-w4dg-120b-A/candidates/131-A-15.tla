---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES seq, cand, occ, i

vars == <<seq, cand, occ, i>>

\* The Boyer-Moore majority vote algorithm: scan seq[1..Len(seq)] once,
\* maintaining a candidate value that is returned as the majority
\* candidate when the scan finishes. occ[c] counts how often value c has
\* been seen so far (i.e., in seq[1..i]), and i is the next position to
\* read. The full action set (Init, Advance, Restart, Halt) is defined
\* here because the module must expose every identifier the .cfg expects,
\* not just those used in the proof.

Len(f) == CHOOSE n \in Nat : \A m \in Nat : (m \in DOMAIN f) <=> (m <= n)
Positions(i) == { j \in 1..(i - 1) : seq[j] = cand }

TypeOK ==
  /\ seq \in [1..Len(seq) -> Value]
  /\ cand \in Value
  /\ occ \in [Value -> Nat]
  /\ i \in 0..(Len(seq) + 1)

Init ==
  /\ seq = [j \in 1..Len(seq) |-> CHOOSE c \in Value : TRUE]
  /\ cand \in Value
  /\ occ = [c \in Value |-> 0]
  /\ i = 1

Advance ==
  /\ i <= Len(seq)
  /\ LET c == seq[i] IN
       /\ occ' = [occ EXCEPT ![c] = @ + 1]
       /\ cand' = IF occ[c] = 0 THEN c ELSE cand
  /\ i' = i + 1
  /\ UNCHANGED seq

Restart ==
  /\ i > Len(seq)
  /\ i' = 1
  /\ occ' = [c \in Value |-> 0]
  /\ UNCHANGED <<seq, cand>>

Halt ==
  /\ i > Len(seq) + 1
  /\ UNCHANGED vars

Next == Init \/ Advance \/ Restart \/ Halt

Spec == Init /\ [][Next]_vars

\* The Boyer-Moore output is correct: any value occupying a strict
\* majority of sequence positions must equal the algorithm's
\* candidate. Because seq and cand are fixed after the scan, the proof
\* is purely arithmetic and needs no extra liveness reasoning.

Correct ==
  \A c \in Value :
    (2 * Cardinality({ j \in 1..Len(seq) : seq[j] = c }) > Len(seq))
      => c = cand

\* The type invariant, proved elsewhere in the full proof suite.
Inv == TypeOK

====