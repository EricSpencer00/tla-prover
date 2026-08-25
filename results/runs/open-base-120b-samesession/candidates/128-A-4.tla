---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*--------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\*--------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*--------------------------------------------------------------------
\* Operator: LimitedSeq  (finite version of Seq, limited by MaxSeqLen)
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\*--------------------------------------------------------------------
\* Types
\*--------------------------------------------------------------------
Interval == [lo : Nat, hi : Nat]

\*--------------------------------------------------------------------
\* Variables
\*--------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Domain(s) == 1 .. Len(s)

MultiSet(s) == [v \in Values |-> Cardinality({ i \in Domain(s) : s[i] = v })]

Permutes(s1, s2) == MultiSet(s1) = MultiSet(s2)

Sorted(s) == \A i, j \in Domain(s) : i < j => s[i] <= s[j]

\* Partition operator: all sequences that could result from a valid
\* partition of interval "intv" around pivot "p".
Partition(old, intv, p) ==
  { new \in LimitedSeq(Values) :
        Len(new) = Len(old)
    /\ \A j \in Domain(old) :
          (j < intv.lo \/ j > intv.hi) => new[j] = old[j]
    /\ \A i \in intv.lo .. p :
          \A j \in p+1 .. intv.hi :
                new[i] <= new[j]
    /\ Permutes(old, new) }

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Loop"

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E intv \in work :
           \/ /\ intv.lo = intv.hi
              /\ work' = work \ {intv}
              /\ UNCHANGED <<seq, orig, pc>>
           \/ /\ intv.lo # intv.hi
              /\ \E p \in intv.lo .. intv.hi :
                    \E new \in Partition(seq, intv, p) :
                       /\ seq' = new
                       /\ let lower == [lo |-> intv.lo, hi |-> p] in
                          let upper == [lo |-> p+1, hi |-> intv.hi] in
                          work' =
                              (work \ {intv})
                              \cup (IF lower.lo <= lower.hi THEN {lower} ELSE {})
                              \cup (IF upper.lo <= upper.hi THEN {upper} ELSE {})
                       /\ orig' = orig
                       /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<seq, orig, work, pc>> /\ WF_<<seq, orig, work, pc>>(Next)

\*--------------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------------
TypeOK ==
  /\ Values \subseteq Int
  /\ MaxSeqLen \in Nat
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq { [lo |-> l, hi |-> h] :
                      l \in Nat /\ h \in Nat /\ l <= h /\ h <= Len(seq) }
  /\ pc \in {"Loop", "Done"}

\*--------------------------------------------------------------------
\* General invariant (preserves permutation)
\*--------------------------------------------------------------------
Inv == Permutes(orig, seq)

\*--------------------------------------------------------------------
\* Partial correctness (post‑condition)
\*--------------------------------------------------------------------
PCorrect == (pc = "Done") => (Sorted(seq) /\ Permutes(orig, seq))

\*--------------------------------------------------------------------
\* Termination property
\*--------------------------------------------------------------------
Termination == <> (pc = "Done")

====