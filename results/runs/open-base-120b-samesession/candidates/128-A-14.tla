---- MODULE Quicksort ----
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Bounded version of Seq (used by the .cfg file to replace Seq)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Helper definitions

Count(seq, v) == Cardinality({ i \in 1..Len(seq) : seq[i] = v })

IsPermutation(s1, s2) ==
  \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(seq) ==
  \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

Partition(s, interval, p) ==
  { s2 \in LimitedSeq(Values) :
      /\ Len(s2) = Len(s)
      /\ \A j \in 1..Len(s) :
           (j < interval.low \/ j > interval.high) => s2[j] = s[j]
      /\ \A j \in interval.low .. p :
           \A k \in p+1 .. interval.high :
               s2[j] <= s2[k] }

\* ----------------------------------------------------------------------
\* PlusCal algorithm (the translation provides Init, Next, pc, etc.)

(*--algorithm Quicksort
variables seq, orig, work;
begin
  choose seq \in LimitedSeq(Values);
  orig := seq;
  work := { [low |-> 1, high |-> Len(seq)] };
  while (work # {}) do
    with i \in work do
      if i.low = i.high then
        work := work \ {i};
      else
        with p \in i.low .. i.high do
          let lower == [low |-> i.low, high |-> p-1];
              upper == [low |-> p+1, high |-> i.high];
          with newSeq \in Partition(seq, i, p) do
            seq := newSeq;
            work := (work \ {i}) \cup { lower, upper };
          end with;
        end with;
      end if;
    end with;
  end while;
end algorithm; *)

\* ----------------------------------------------------------------------
\* Invariants

TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq
        { i \in [low : Nat, high : Nat] :
            /\ i.low >= 1
            /\ i.high >= i.low
            /\ i.high <= Len(seq) }

Perm == IsPermutation(seq, orig)

Inv == /\ TypeOK /\ Perm

PCorrect == (work = {} => /\ IsPermutation(seq, orig) /\ Sorted(seq))

\* ----------------------------------------------------------------------
\* Specification

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Liveness property (termination)

Termination == <> (work = {})

=============================================================================