---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*-------------------------------------------------
\* Constants
\*-------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*-------------------------------------------------
\* Operator: LimitedSeq
\* A finite version of Seq restricted by MaxSeqLen
\*-------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\*-------------------------------------------------
\* Variables
\*-------------------------------------------------
VARIABLES seq, orig, work, pc

\*-------------------------------------------------
\* Helper definitions
\*-------------------------------------------------
\* Intervals are represented as pairs <<lo,hi>>
Interval == <<lo, hi>> \* where lo,hi \in Nat
Intervals == { <<lo, hi>> : lo \in Nat /\ hi \in Nat /\ lo <= hi }

\* Subsequence of a sequence from lo to hi (inclusive)
Sub(seq_, lo, hi) == [i \in lo..hi |-> seq_[i]]

\* Count occurrences of a value v in a (sub)sequence s
Count(v, s) == Cardinality({ i \in DOMAIN s : s[i] = v })

\* Permutation predicate for two sequences (or subsequences)
Permutes(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values : Count(v, s1) = Count(v, s2)

\* Predicate stating that seq' is a valid partition of seq over
\* the interval [lo..hi] with pivot p
Partition(seq_, seqPrime, lo, hi, p) ==
    /\ \A i \in 1..Len(seq_) :
          (i < lo \/ i > hi) => seqPrime[i] = seq_[i]
    /\ \A i \in lo..p : \A j \in p+1..hi : seqPrime[i] <= seqPrime[j]
    /\ Permutes(Sub(seq_, lo, hi), Sub(seqPrime, lo, hi))

\* Sortedness of a sequence
Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\*-------------------------------------------------
\* Initial state
\*-------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ seq # <<>>
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\*-------------------------------------------------
\* Next-state relation
\*-------------------------------------------------
ProcessInterval ==
    /\ work # {}
    /\ \E interval \in work :
          LET lo == interval[1] IN hi == interval[2] IN
          /\ IF lo = hi THEN
                 (* singleton interval: just remove it *)
                 /\ work' = work \ {interval}
                 /\ seq' = seq
             ELSE
                 (* non‑singleton interval *)
                 /\ \E p \in lo..hi :
                        /\ Partition(seq, seqPrime, lo, hi, p)
                        /\ let lower  == IF lo <= p-1 THEN { <<lo, p-1>> } ELSE {}
                           upper  == IF p+1 <= hi THEN { <<p+1, hi>> } ELSE {}
                           newInts == lower \cup upper in
                        /\ work' = (work \ {interval}) \cup newInts
                        /\ seq' = seqPrime
          /\ orig' = orig
          /\ pc' = "Loop"

Terminate ==
    /\ work = {}
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work>>

StutterAfterDone ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
    \/ ProcessInterval
    \/ Terminate
    \/ StutterAfterDone

\*-------------------------------------------------
\* Specification
\*-------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>> /\ WF_<<seq, orig, work, pc>>(Next)

\*-------------------------------------------------
\* Invariants
\*-------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq Intervals
    /\ \A interval \in work :
          LET lo == interval[1] IN hi == interval[2] IN
          /\ 1 <= lo /\ lo <= hi /\ hi <= Len(seq)
    /\ pc \in {"Loop", "Done"}

Inv ==
    /\ Permutes(orig, seq)
    /\ \A interval \in work :
          LET lo == interval[1] IN hi == interval[2] IN
          /\ \A i \in lo..hi-1 :
                \A j \in i+1..hi :
                    seq[i] <= seq[j]   \* not required for correctness but safe

PCorrect ==
    (pc = "Done") => (Sorted(seq) /\ Permutes(orig, seq))

\*-------------------------------------------------
\* Properties
\*-------------------------------------------------
Termination == <> (pc = "Done")

\*-------------------------------------------------
\* The set of invariants and properties used by the
\* model checker (as listed in the .cfg file)
\*-------------------------------------------------
\* INVARIANTS: PCorrect, TypeOK, Inv
\* PROPERTIES: Termination

====