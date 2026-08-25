---- MODULE Quicksort ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Finite version of Seq, to be used in the model
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Variable seq, orig, work, pc

Interval == [lo : Nat, hi : Nat]

ValidInterval(i) == 
    /\ i.lo >= 1
    /\ i.hi <= Len(seq)
    /\ i.lo <= i.hi

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Permutation(a, b) ==
    \A v \in Values :
        Cardinality({ i \in 1..Len(a) : a[i] = v }) =
        Cardinality({ i \in 1..Len(b) : b[i] = v })

Partition(oldSeq, I, p) ==
    { s \in LimitedSeq(Values) :
        /\ Len(s) = Len(oldSeq)
        /\ \A i \in 1..Len(oldSeq) :
              (i < I.lo \/ i > I.hi) => s[i] = oldSeq[i]
        /\ \A i \in I.lo..p :
              \A j \in p+1..I.hi : s[i] <= s[j]
        /\ Permutation(oldSeq, s)
    }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values)
    /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { [lo |-> 1, hi |-> Len(seq)] }
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
RunStep ==
    /\ pc = "Run"
    /\ work # {}
    /\ \E I \in work :
          /\ I.lo = I.hi
          /\ /\ work' = work \ {I}
             /\ UNCHANGED <<seq, orig>>
          \/ /\ I.lo # I.hi
             /\ \E p \in I.lo..I.hi :
                  /\ \E s \in Partition(seq, I, p) :
                       /\ seq' = s
                       /\ work' = (work \ {I})
                           \cup (IF I.lo <= p-1 THEN { [lo |-> I.lo, hi |-> p-1] } ELSE {})
                           \cup (IF p+1 <= I.hi THEN { [lo |-> p+1, hi |-> I.hi] } ELSE {})
                       /\ UNCHANGED orig
    /\ pc' = "Run"

Terminate ==
    /\ pc = "Run"
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

StutterAfterDone ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
    \/ RunStep
    \/ Terminate
    \/ StutterAfterDone

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq { i \in Interval : ValidInterval(i) }
    /\ pc \in {"Run", "Done"}

Inv ==
    /\ Permutation(seq, orig)
    /\ \A i \in work : ValidInterval(i)
    /\ (pc = "Done" => \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j])

PCorrect ==
    (pc = "Done") => (Permutation(seq, orig) /\ \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j])

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====