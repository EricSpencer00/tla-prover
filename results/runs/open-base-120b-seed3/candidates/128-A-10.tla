---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
Count(seq, v) ==
  Cardinality({ k \in 1..Len(seq) : seq[k] = v })

IsPermutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \A v \in Values : Count(s, v) = Count(t, v)

Sorted(seq) ==
  \A i \in 1..Len(seq)-1 : seq[i] <= seq[i+1]

LimitedSeq(V) ==
  { s \in Seq(V) : Len(s) <= MaxSeqLen }

Partition(s, i, j, p) ==
  { s2 \in Seq(Values) :
      /\ Len(s2) = Len(s)
      /\ \A k \in 1..Len(s) :
           (k < i \/ k > j) => s2[k] = s[k]
      /\ \A a \in i..p : \A b \in p+1..j : s2[a] <= s2[b]
      /\ \A v \in Values : Count(s2, v) = Count(s, v) }

\* ---------- Variables ----------
VARIABLES seq, orig, workSet, pc

\* ---------- State predicates ----------
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ Len(seq) > 0
  /\ orig = seq
  /\ workSet = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* Next-step relation
Next ==
  \/ /\ pc = "Loop"
     /\ workSet # {}
     /\ \E I \in workSet :
          LET i == I[1] IN j == I[2] IN
          IF i = j THEN
            /\ seq' = seq
            /\ orig' = orig
            /\ workSet' = workSet \ {I}
            /\ pc' = "Loop"
          ELSE
            /\ \E p \in i..j :
                 LET lower == IF i <= p-1 THEN {<<i, p-1>>} ELSE {} IN
                 LET upper == IF p+1 <= j THEN {<<p+1, j>>} ELSE {} IN
                 /\ seq' \in Partition(seq, i, j, p)
                 /\ orig' = orig
                 /\ workSet' = (workSet \ {I}) \cup lower \cup upper
                 /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ workSet = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, workSet>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, workSet, pc>>

\* ---------- Invariants ----------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ workSet \subseteq { <<i, j>> : i \in 1..Len(seq), j \in i..Len(seq) }
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ IsPermutation(seq, orig)
  /\ \A i, j \in 1..Len(seq) :
        (i < j) /\ ~(\E I \in workSet : i \in I /\ j \in I) => seq[i] <= seq[j]

PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ IsPermutation(seq, orig))

\* ---------- Specification ----------
vars == <<seq, orig, workSet, pc>>
Spec ==
  Init /\ [][Next]_vars

\* ---------- Property ----------
Termination == <> (pc = "Done")

=============================================================================