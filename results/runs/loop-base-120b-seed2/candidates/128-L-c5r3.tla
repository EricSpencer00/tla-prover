---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
Count(s, v) ==
  Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s1, s2) ==
  \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
  Len(s) <= 1 \/ \A i \in 1..(Len(s) - 1) : s[i] <= s[i+1]

Intervals(seq) ==
  { <<lo, hi>> :
      (lo \in 1..Len(seq)) /\ (hi \in lo..Len(seq)) }

Partition(s, lo, hi, p) ==
  { s2 \in Seq(Values) :
      (Len(s2) = Len(s)) /\
      (\A k \in 1..Len(s) : (k < lo \/ k > hi) => s2[k] = s[k]) /\
      (\A i \in lo..p : \A j \in p+1..hi : s2[i] <= s2[j]) /\
      (\A v \in Values : Count(s, v) = Count(s2, v)) }

LimitedSeq(V) ==
  { s \in Seq(V) : Len(s) \in 1..MaxSeqLen }

\* ---------- Variables ----------
VARIABLES seq, orig, work, pc

\* ---------- State predicates ----------
TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq Intervals(seq)
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ TypeOK
  /\ Permutation(seq, orig)

PCorrect ==
  pc = "Done" => (Sorted(seq) /\ Permutation(seq, orig))

\* ---------- Initial state ----------
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* ---------- Next-state relation ----------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E i \in work :
          LET lo == i[1] IN
          LET hi == i[2] IN
          IF lo = hi THEN
            (work' = work \ {i}) /\
            (seq'   = seq) /\
            (pc'    = "Loop") /\
            UNCHANGED <<orig>>
          ELSE
            /\ \E p \in lo..hi :
                  LET lower ==
                        IF lo <= p - 1 THEN { <<lo, p - 1>> } ELSE {}
                  IN
                  LET upper ==
                        IF p + 1 <= hi THEN { <<p + 1, hi>> } ELSE {}
                  IN
                  (seq' \in Partition(seq, lo, hi, p)) /\
                  (work' = (work \ {i}) \cup lower \cup upper) /\
                  (pc'   = "Loop") /\
                  UNCHANGED <<orig>>
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ---------- Specification ----------
vars == <<seq, orig, work, pc>>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ---------- Properties ----------
Termination == <> (pc = "Done")

\* ---------- Invariants for the model checker ----------
INVARIANT PCorrect
INVARIANT TypeOK
INVARIANT Inv

\* ---------- Property for the model checker ----------
PROPERTY Termination
====