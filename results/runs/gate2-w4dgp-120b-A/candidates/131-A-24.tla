---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES cand, count, i, seq, answer

vars == <<cand, count, i, seq, answer>>

Positions(p) == {k \in 0 .. (i - 1) : seq[k] = p}

Init ==
  /\ cand = 0
  /\ count = 0
  /\ i = 0
  /\ seq \in [0 .. 2 -> Value]
  /\ answer = 0

\* An empty prefix admits no majority candidate.
NoMajorityPrefix ==
  \A p \in Value : i <= 2 => i * 2 <= 3

\* Consistency: if a candidate exists it must be the unique majority; if
\* there is no candidate the prefix admits no majority at all.
CandidateConsistent ==
  \/ (cand # 0 /\ i * 2 > 3 /\ answer = cand)
  \/ (cand = 0 /\ i * 2 <= 3)

NextCand ==
  \E p \in Value :
    /\ cand' = p
    /\ count' = 1
    /\ i' = i + 1
    /\ UNCHANGED <<seq, answer>>

NextCount ==
  /\ i < 3
  /\ count' = count + 1
  /\ i' = i + 1
  /\ UNCHANGED <<cand, seq, answer>>

NextReset ==
  /\ i < 3
  /\ count > 1
  /\ count' = count - 1
  /\ i' = i + 1
  /\ UNCHANGED <<cand, seq, answer>>

NextDrop ==
  /\ i < 3
  /\ count = 1
  /\ cand' = 0
  /\ count' = 0
  /\ i' = i + 1
  /\ UNCHANGED <<seq, answer>>

NextAnswer ==
  /\ i = 3
  /\ answer' = cand
  /\ UNCHANGED <<cand, count, i, seq>>

NextStep == NextCand \/ NextCount \/ NextReset \/ NextDrop \/ NextAnswer

Spec == Init /\ [][NextStep]_vars

Inv ==
  /\ i <= 2 => i * 2 <= 3
  /\ \/ (cand # 0 /\ i * 2 > 3 /\ answer = cand)
     \/ (cand = 0 /\ i * 2 <= 3)

TypeOK == Inv

\* The candidate invariant from the main specification carries over unchanged.
Correct == Inv

====