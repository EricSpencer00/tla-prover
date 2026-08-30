---- MODULE MajorityProof ----
EXTENDS MajorityVote, FiniteSets

CONSTANTS Value

VARIABLES seq, candidate, idx, seen
vars == <<seq, candidate, idx, seen>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value \cup {"none"}
  /\ idx \in Nat
  /\ seen \in Nat

Init ==
  /\ seq = << >>
  /\ candidate = "none"
  /\ idx = 0
  /\ seen = 0

Append(v) ==
  /\ seq' = Append(seq, v)
  /\ UNCHANGED <<candidate, idx, seen>>

Initialize(c) ==
  /\ seq # << >>
  /\ idx = 0
  /\ candidate' = c
  /\ seen' = 0
  /\ UNCHANGED <<seq, idx>>

Scan(v) ==
  /\ idx < Len(seq)
  /\ seq[idx + 1] = v
  /\ candidate = v
  /\ seen' = seen + 1
  /\ idx' = idx + 1
  /\ UNCHANGED <<seq, candidate>>

Proceed ==
  /\ idx < Len(seq)
  /\ seq[idx + 1] # candidate
  /\ idx' = idx + 1
  /\ UNCHANGED <<seq, candidate, seen>>

Finished ==
  /\ idx = Len(seq)
  /\ UNCHANGED vars

Next ==
  \/ \E v \in Value : Append(v)
  \/ \E c \in Value : Initialize(c)
  \/ \E v \in Value : Scan(v)
  \/ Proceed
  \/ Finished

Spec == Init /\ [][Next]_vars

Majority == seen * 2 > idx

Correct == Majority => candidate = seq[seen + 1]

OccBefore(i) == { seq[j] : j \in 1 .. i }

OccurancesDistinct ==
  /\ OccBefore(1) = {}
  /\ \A i \in 1 .. Len(seq) : OccBefore(i + 1) = OccBefore(i) \cup {seq[i + 1]}

Inv == TypeOK /\ Correct /\ OccurancesDistinct
====