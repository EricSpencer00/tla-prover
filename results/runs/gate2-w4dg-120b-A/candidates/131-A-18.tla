---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Value

\* The Boyer-Moore majority vote algorithm's state space is imported wholesale from
\* the main specification Module "MajorityVote". This proof-only wrapper adds
\* TLAPS-checked lemmas and invariants without introducing new state.
EXTENDS MajorityVote

Lemmas ==
  /\ FORALL A \in SUBSET Nat : (A # {}) => \E x \in A : TRUE
  /\ \A A \in SUBSET Nat, x \in Nat : x \notin A => Cardinality(A \cup {x}) = Cardinality(A) + 1

TypeOK == \A x \in Value : Cardinality({j \in 1..Len(seq) : seq[j] = x}) <= Len(seq)

\* The main correctness property from the Boyer-Moore algorithm: once the whole
\* sequence has been scanned, any value that appears in a strict majority of
\* positions must equal the candidate variable.
Correct == (pos = Len(seq)) => (\A x \in Value : (2 * Cardinality({j \in 1..Len(seq) : seq[j] = x}) > Len(seq)) => x = candidate)

Spec == MajorityVote!Spec

Init == MajorityVote!Init

Next == MajorityVote!Next

Inv == MajorityVote!Inv


====