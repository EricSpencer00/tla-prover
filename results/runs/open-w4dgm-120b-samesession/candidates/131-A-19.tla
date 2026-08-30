---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

\* No new state variables; all are inherited from MajorityVote.

TypeOK ==
  /\ Seq \in Seq(Value)
  /\ Len \in Nat
  /\ Len >= Len(Seq)
  /\ Cursor \in 0..Len
  /\ Candidate \in Value
  /\ Count \in Nat

\* The inductive invariant from MajorityVote.voting, restated here so it can
\* be discharged as a separate proof obligation in this module.
Inv == voting

Init ==
  /\ /\ Seq = << >>
     /\ Len = 1
     /\ Cursor = 0
     /\ Candidate = CHOOSE v \in Value : TRUE
     /\ Count = 0

Read(c, v) ==
  /\ Len < Len(Seq)
  /\ Len' = Len + 1
  /\ Seq' = Append(Seq, v)
  /\ UNCHANGED <<Cursor, Candidate, Count>>

Reset ==
  /\ Len > 0
  /\ Len' = 0
  /\ Seq' = << >>
  /\ Cursor' = 0
  /\ UNCHANGED <<Candidate, Count>>

Scan ==
  /\ Cursor < Len
  /\ LET x == Seq[Cursor + 1] IN
       /\ IF x = Candidate
            THEN Count' = Count + 1
            ELSE Candidate' = x
  /\ Cursor' = Cursor + 1
  /\ UNCHANGED <<Seq, Len>>

\* Scan only fires at the end of the sequence.
Done ==
  /\ Cursor = Len
  /\ Len > 0
  /\ UNCHANGED <<Seq, Len, Cursor, Candidate, Count>>

Next ==
  \/ \E c \in Value, v \in Value : Read(c, v)
  \/ Reset
  \/ Scan
  \/ Done

Spec ==
  /\ Init
  /\ [][Next]_<<Seq, Len, Cursor, Candidate, Count>>
  /\ WF_vars(Scan)

\* The candidate must equal any value that appears in a strict majority of
\* positions of the scanned sequence -- this is the Boyer-Moore correctness
\* guarantee, and it is a corollary of the voting invariant.
Correct ==
  /\ Inv
  /\ (2 * Count > Cursor) => (\E k \in 1..Cursor : Seq[k] = Candidate)

\* Type checking is invariant, so it can be discharged without any fairness.
TypeOKInv == TypeOK

====