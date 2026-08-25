---- MODULE Quicksort ----
EXTENDS Sequences, Naturals, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

SubIntervals(n) == { <<i, j>> : 1 <= i /\ i <= j /\ j <= n }

Count(v, s) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \A v \in Values : Count(v, s) = Count(v, t)

IsSorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* ---------- Variables ----------
VARIABLES seq, orig, work, pc
vars == << seq, orig, work, pc >>

\* ---------- State predicates ----------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq SubIntervals(Len(seq))
  /\ pc \in {"Loop", "Done"}

PCorrect ==
  (pc = "Done") => (IsSorted(seq) /\ Permutation(seq, orig))

Inv == 
  /\ TypeOK
  /\ (pc = "Loop" => work # {})

\* ---------- Initial state ----------
Init ==
  /\ seq \in LimitedSeq(Values) /\ seq # << >>
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* ---------- Next-state relation ----------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E I \in work :
          LET i == I[1], j == I[2] IN
          IF i = j THEN
            /\ work' = work \ {I}
            /\ UNCHANGED << seq, orig, pc >>
          ELSE
            /\ \E p \in i..j :
                 /\ \E newseq \in LimitedSeq(Values) :
                      /\ Len(newseq) = Len(seq)
                      /\ \A k \in 1..Len(seq) :
                            IF (k < i) \/ (k > j) THEN newseq[k] = seq[k] ELSE TRUE
                      /\ \A a \in i..p : \A b \in p+1..j : newseq[a] <= newseq[b]
                      /\ Permutation(newseq, seq)
                      /\ seq' = newseq
                      /\ work' = (work \ {I}) \cup { <<i, p>>, <<p+1, j>> }
                      /\ UNCHANGED << orig, pc >>
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED << seq, orig, work >>
  \/ /\ pc = "Done"
     /\ UNCHANGED vars

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Properties ----------
Termination == <> (pc = "Done")

====