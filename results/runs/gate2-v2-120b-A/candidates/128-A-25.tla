---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------------------
  Constants (to be instantiated in the .cfg)
-----------------------------------------------------------------------------*)
CONSTANTS Values, MaxSeqLen, Seq

(*-----------------------------------------------------------------------------
  Types
-----------------------------------------------------------------------------*)
VARIABLES seq, origSeq, work, pc

(* seq    : the current sequence being sorted, a function from 1..Len to Values
   origSeq: a copy of the initial sequence, never changed
   work   : a set of intervals that still need processing; each interval is a
            pair <<lo, hi>> with 1 <= lo <= hi <= Len(seq)
   pc     : program counter, either "Running" or "Terminated"
-----------------------------------------------------------------------------*)

(* Helper definitions *)
Len == Len(seq)

(* An interval is represented as a pair <<lo, hi>> *)
Interval == [lo : Nat, hi : Nat]

(*----------------------------------------------------------------------------- 
  Initial predicate
-----------------------------------------------------------------------------*)
Init ==
  /\ seq \in Seq /\ Len(seq) > 0
  /\ origSeq = seq
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "Running"

(*----------------------------------------------------------------------------- 
  Partition action (abstract)
  Choose a new sequence that is a valid partition of the current interval.
-----------------------------------------------------------------------------*)
PartitionResult(old, lo, hi, pivot) ==
  \E newSeq \in Seq :
    /\ Len(newSeq) = Len(old)
    /\ \A i \in 1..Len(old) :
         (i < lo \/ i > hi) => newSeq[i] = old[i]
    /\ \A i \in lo..pivot :
         \A j \in (pivot+1)..hi =>
            newSeq[i] <= newSeq[j]
    /\ \E perm \in Permutations(Values) :
         /\ \A i \in lo..hi : newSeq[i] = perm(old[i])
         /\ (newSeq \ {i \in lo..hi} = old \ {i \in lo..hi})

(* A generic permutation (bijection) on Values *)
Permutations(S) == { f \in [S -> S] : \A x, y \in S : f[x] = f[y] => x = y }

(*----------------------------------------------------------------------------- 
  One iteration of the sorting loop
-----------------------------------------------------------------------------*)
Step ==
  \/ /\ pc = "Running"
        /\ work = {}
        /\ pc' = "Terminated"
        /\ UNCHANGED <<seq, origSeq, work>>
  \/ /\ pc = "Running"
        /\ work # {}
        /\ \E int \in work :
           LET lo == int[1] IN
           LET hi == int[2] IN
           /\ IF lo = hi
                THEN /\ seq' = seq
                     /\ work' = work \ {int}
                ELSE 
                /\ \E pivot \in lo..hi :
                     LET lower == <<lo, pivot>> IN
                     LET upper == <<pivot+1, hi>> IN
                     /\ \E newSeq \in PartitionResult(seq, lo, hi, pivot) :
                          /\ seq' = newSeq
                          /\ work' = (work \ {int}) \cup {lower, upper}
           /\ pc' = "Running"
           /\ UNCHANGED origSeq

Next == Step

(*----------------------------------------------------------------------------- 
  Specification
-----------------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, origSeq, work, pc>>

(*----------------------------------------------------------------------------- 
  Type correctness invariant
-----------------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq
  /\ origSeq \in Seq
  /\ work \subseteq {<<lo, hi>> : lo, hi \in Nat /\ 1 <= lo /\ lo <= hi /\ hi <= Len(seq)}
  /\ pc \in {"Running", "Terminated"}

(*----------------------------------------------------------------------------- 
  Safety invariant: when terminated, seq is sorted and a permutation of origSeq
-----------------------------------------------------------------------------*)
Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

PermutationOf(s, t) ==
  \E perm \in Permutations(Values) : \A i \in 1..Len(s) : s[i] = perm(t[i])

PCorrect ==
  (pc = "Terminated") => (Sorted(seq) /\ PermutationOf(seq, origSeq))

(*----------------------------------------------------------------------------- 
  Additional invariant used in the textbook proof (optional concrete form)
-----------------------------------------------------------------------------*)
Inv ==
  /\ TypeOK
  /\ PCorrect

(*----------------------------------------------------------------------------- 
  Termination property (derived from weak fairness on Next)
-----------------------------------------------------------------------------*)
Termination == <> (pc = "Terminated")

=============================================================================