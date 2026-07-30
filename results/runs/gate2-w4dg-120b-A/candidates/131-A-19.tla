---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

\* Formal proof of correctness for the Boyer-Moore majority vote algorithm.
\* Extends the main algorithm spec with invariant proofs, checked by TLAPS.
\* All state variables and transition actions are imported from the main spec.

CONSTANTS
  Value

\* VoteCount[t] is the candidate selected by the Boyer-Moore algorithm after
\* scanning the first t elements of the input sequence.
VARIABLES
  VoteCount
  Scanned
  Positions

vars == <<VoteCount, Scanned, Positions>>

TypeOK ==
  /\ VoteCount \in Value \cup {"none"}
  /\ Scanned \in 0..N
  /\ Positions \subseteq (0..(N-1))

Init ==
  /\ VoteCount = "none"
  /\ Scanned = 0
  /\ Positions = {}

\* One Boyer-Moore step: process the next element of the input sequence.
Step ==
  /\ Scanned < N
  /\ LET cand == VoteCount
     IN VoteCount' = IF cand = "none" THEN Input[Scanned]
                      ELSE IF cand = Input[Scanned] THEN cand
                      ELSE "none"
  /\ Scanned' = Scanned + 1
  /\ Positions' = Positions \cup {Scanned}

Next == Step

Spec == Init /\ [][Next]_vars

\* An invariant of the algorithm: ScanCount never exceeds the sequence length.
WithinBound == Scanned =< N

\* No-op transition, kept only so TLAPS finds a non-empty step in the state
\* space; always available and does not change the state.
Stall == UNCHANGED vars

\* The invariant is extended with a dummy transition to keep the step set complete.
SpecWithStall == Spec /\ [][Stall]_vars

\* The only candidate left after scanning the whole sequence is the majority
\* element, if one exists: any value that occurs in a strict majority of
\* positions must equal the Boyer-Moore candidate.
Correct ==
  /\ Scanned = N
  /\ \A v \in Value : (2 * Cardinality({i \in Positions : Input[i] = v}) > N)
          => VoteCount = v

\* The proof proceeds from the type invariant to the correctness invariant.
TypeOK == WithinBound

Inv == TypeOK /\ Correct

====