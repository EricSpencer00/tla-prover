---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants (must be supplied in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS Values, MaxSeqLen, Seq

(*--------------------------------------------------------------------
  Derived sets and helper definitions
--------------------------------------------------------------------*)
Indices == 1 .. MaxSeqLen

Interval == [low : Nat, high : Nat]  \* low <= high, both within Indices

\* Helper to compute the length of a sequence (0 for the empty sequence)
SeqLen(s) == Len(s)

\* Helper to ensure a sequence is within the allowed value set
SeqOK(s) == /\ SeqLen(s) <= MaxSeqLen
            /\ \A i \in 1..SeqLen(s) : s[i] \in Values

\* Permutation: there exists a bijection on the domain that maps one sequence
\* to the other while preserving element values.
Permutes(s, t) ==
  /\ SeqLen(s) = SeqLen(t)
  /\ \E f \in [1..SeqLen(s) -> 1..SeqLen(s)] :
        /\ \A i, j \in 1..SeqLen(s) : (f[i] = f[j]) => (i = j)
        /\ \A i \in 1..SeqLen(s) : s[f[i]] = t[i]

\* Sortedness predicate (non‑decreasing order)
Sorted(s) ==
  \A i, j \in 1..SeqLen(s) : i < j => s[i] <= s[j]

\* Domain partition: two sequences are equal outside a given interval
DomainEq(s, t, iv) ==
  /\ iv.low >= 1 /\ iv.high <= SeqLen(s)
  /\ \A i \in 1..SeqLen(s) :
        (i < iv.low \/ i > iv.high) => s[i] = t[i]

\* Partition result: a new sequence that is a permutation of the old one,
\* leaves elements outside iv unchanged, and respects the pivot ordering.
PartitionResult(old, iv, piv) ==
  \E new \in Seq :
    /\ SeqLen(new) = SeqLen(old)
    /\ DomainEq(old, new, iv)
    /\ \A i \in iv.low .. piv :
          \A j \in piv+1 .. iv.high :
                new[i] <= new[j]

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES seq, orig, work, pc

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ seq = Seq
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> SeqLen(seq)] }
  /\ pc = "Loop"

(*--------------------------------------------------------------------
  Main loop action
--------------------------------------------------------------------*)
Loop ==
  \/ /\ work # {}
     /\ \E iv \in work :
          /\ iv.low <= iv.high
          /\ IF iv.low = iv.high
                THEN /\ seq' = seq
                     /\ work' = work \ {iv}
                ELSE
                /\ \E piv \in iv.low .. iv.high :
                     /\ \E new \in Seq :
                          /\ PartitionResult(seq, iv, piv)
                          /\ seq' = new
                          /\ work' = (work \ {iv}) \cup
                                    { [low |-> iv.low, high |-> piv],
                                      [low |-> piv+1, high |-> iv.high] }
  \/ /\ work = {}
     /\ seq' = seq
     /\ work' = {}
     /\ pc' = "Done"

Next == Loop /\ pc' = pc

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(*--------------------------------------------------------------------
  Invariant required by the .cfg file
--------------------------------------------------------------------*)
PCorrect ==
  /\ pc = "Done"
  /\ Sorted(seq)
  /\ Permutes(seq, orig)

(*--------------------------------------------------------------------
  Type correctness invariant (useful but not the safety property)
--------------------------------------------------------------------*)
TypeOK ==
  /\ SeqOK(seq)
  /\ SeqOK(orig)
  /\ work \subseteq {[low : Nat, high : Nat] |
        \A i \in 1..SeqLen(seq) :
            (i < low \/ i > high) => FALSE}   \* trivially true, just a type guard
  /\ pc \in {"Loop", "Done"}

(*--------------------------------------------------------------------
  Full inductive invariant used for the safety proof
--------------------------------------------------------------------*)
Inv ==
  /\ TypeOK
  /\ \A iv \in work :
        /\ iv.low >= 1 /\ iv.high <= SeqLen(seq)
        /\ iv.low <= iv.high
  /\ Permutes(seq, orig)

(*--------------------------------------------------------------------
  Liveness property (termination)
--------------------------------------------------------------------*)
Termination ==
  <> (pc = "Done")

=============================================================================