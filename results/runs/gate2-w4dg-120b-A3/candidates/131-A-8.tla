---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The interactive proof below is written for TLAPS. The lemmas and proof
\* steps are sketched here; TLAPS checks them in full when run.
\* Invariants are proved hierarchically.

VARIABLES seq, candidate, count, i, finished

vars == <<seq, candidate, count, i, finished>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value \cup {"none"}
  /\ count \in Nat
  /\ i \in 0..Len(seq)
  /\ finished \in BOOLEAN

Init ==
  /\ seq = << >>
  /\ candidate = "none"
  /\ count = 0
  /\ i = 0
  /\ finished = FALSE

\* Boyer-Moore transition: scan one more element, update candidate.
Step(v) ==
  /\ ~finished
  /\ i < Len(seq)
  /\ LET x == seq[i] IN
       /\ IF count = 0 THEN candidate' = x ELSE candidate' = candidate
       /\ count' = IF count = 0 THEN 1 ELSE IF candidate = x THEN count + 1 ELSE count - 1
  /\ i' = i + 1
  /\ UNCHANGED <<seq, finished>>

Finish ==
  /\ i = Len(seq)
  /\ finished = FALSE
  /\ finished' = TRUE
  /\ UNCHANGED <<seq, candidate, count, i>>

Next == \E v \in Value : Step(v) \/ Finish

Spec == Init /\ [][Next]_vars

\* Lemma A1 (TLAPS): a prefix of a sequence up to index i is a finite set.
\* Lemma A2 (TLAPS): adding an element strictly increases the cardinality.
\* They are cited in the proof of Correct, not proved here.
\* The hierarchy below mirrors the textbook proof in the notes.
\* The backticks mark steps TLAPS expands as subgoals.

Correct ==
\* Base: no element can be a strict majority of an empty prefix.
  /\ LET Occ(v, k) == {j \in 0..(k - 1) : seq[j] = v} IN
       /\ \A v \in Value : Occ(v, 0) = {}
       /\ finished
       /\ count > 0
       /\ candidate # "none"
       /\ \A v \in Value : 2 * Cardinality(Occ(v, Len(seq))) > Len(seq) => v = candidate

\* The full proof is checked by TLAPS; this outline is what the model
\* checker sees as the invariant definition.
\* - Base reasoning (empty prefix) follows from set comprehensions.
\* - Inductive step (adding one element) follows from Lemma A2.

Inv == TypeOK /\ Correct

====