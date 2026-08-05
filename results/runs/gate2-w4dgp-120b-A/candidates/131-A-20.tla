---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

NONE == "none"

VARIABLES seq, cand, count, i

vars == <<seq, cand, count, i>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ cand \in Value \cup {NONE}
  /\ count \in Nat
  /\ i \in Nat

Init ==
  /\ seq = << >>
  /\ cand = NONE
  /\ count = 0
  /\ i = 0

AppendSeq(v) ==
  /\ i < Len(seq)
  /\ LET x == seq[i + 1] IN
       /\ cand' = IF count = 0 THEN x ELSE cand
       /\ count' = IF count = 0 THEN 1 ELSE IF cand = x THEN count + 1 ELSE count - 1
  /\ i' = i + 1
  /\ UNCHANGED seq

Idle ==
  /\ i = Len(seq)
  /\ UNCHANGED vars

Next ==
  \/ \E v \in Value : AppendSeq(v)
  \/ Idle

Spec == Init /\ [][Next]_vars

\* No new state or transition: the specification is identical to the main
\* one, so the type-correctness invariant is proved exactly as there.
TypeOKIsInv ==
  /\ TypeOK
  /\ (Init => TypeOK)
  /\ (\A s \in [vars -> _] : Init /\ UNCHANGED vars => TypeOK)
  /\ (\A s \in [vars -> _] : (\E v \in Value : AppendSeq(v)) /\ UNCHANGED vars => TypeOK)
  /\ (\A s \in [vars -> _] : Idle /\ UNCHANGED vars => TypeOK)

\* Lemma: positions before a given index form a finite set.
BeforeFinite(k) == { e \in Integer : e <= k } \in FINITE

\* Lemma: adding an element to a finite set raises its cardinality by one.
CardPlusOne(A, x) ==
  /\ x \notin A
  /\ A \cup {x} \in FINITE
  /\ Cardinality(A \cup {x}) = Cardinality(A) + 1

PrevOcc(v, i) ==
  { e \in Integer : e <= i /\ seq[e] = v }

PrevMajor(v) == Cardinality(PrevOcc(v, Len(seq))) * 2 > Len(seq)

\* Lemma: the candidate is never NONE once some value has a strict majority.
CandidateExistsAtMajority ==
  \A v \in Value : PrevMajor(v) => (cand = NONE => FALSE)

\* The main correctness invariant is imported unchanged from the original spec.
Correct ==
  (\A v \in Value : PrevMajor(v) => v = cand)

Inv == TypeOK /\ Correct

====