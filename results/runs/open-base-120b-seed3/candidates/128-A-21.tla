---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Bounded version of Seq
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Interval definition
INTERVAL == [low : Nat, high : Nat]

INTERVALS == { iv \in INTERVAL : iv.low <= iv.high }

\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
MainStep ==
  /\ pc = "Loop"
  /\ IF work = {}
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<seq, orig, work>>
       ELSE
          \E iv \in work :
            LET low  == iv.low
                high == iv.high
            IN
            IF low = high
               THEN /\ work' = work \ {iv}
                    /\ UNCHANGED <<seq, orig>>
                    /\ pc' = "Loop"
               ELSE
                  \E pivot \in low .. high :
                    \E newSeq \in LimitedSeq(Values) :
                      /\ Len(newSeq) = Len(seq)
                      /\ (\A i \in 1 .. Len(seq) :
                           IF i < low \/ i > high THEN newSeq[i] = seq[i] ELSE TRUE)
                      /\ (\A i \in low .. pivot :
                           \A j \in pivot+1 .. high :
                             newSeq[i] <= newSeq[j])
                      /\ seq' = newSeq
                    /\ pc' = "Loop"
                    LET lower == [low |-> low,   high |-> pivot-1]
                        upper == [low |-> pivot+1, high |-> high]
                    IN
                      work' = (work \ {iv})
                              \cup (IF lower.low <= lower.high THEN {lower} ELSE {})
                              \cup (IF upper.low <= upper.high THEN {upper} ELSE {})

\* ----------------------------------------------------------------------
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == MainStep \/ Stutter

\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq INTERVALS
  /\ \A iv \in work :
        iv.low >= 1 /\ iv.high <= Len(seq) /\ iv.low <= iv.high
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
Permutation(s, t) ==
  LET n == Len(s) IN
    /\ Len(t) = n
    /\ \E f \in [1..n -> 1..n] :
         /\ \A i, j \in 1..n : (f[i] = f[j]) => i = j
         /\ \A i \in 1..n : s[i] = t[f[i]]

Sorted(s) ==
  \A i, j \in 1 .. Len(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
Inv == TypeOK /\ Permutation(seq, orig)

PCorrect == (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* (they are already defined with the exact names)
\* SPECIFICATION formula
Spec

\* INVARIANTS
PCorrect
TypeOK
Inv

\* PROPERTIES
Termination

====