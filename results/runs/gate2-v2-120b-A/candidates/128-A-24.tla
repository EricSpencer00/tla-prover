---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

(* ----------------------------------------------------------------------
   Derived constants and helper definitions
   ---------------------------------------------------------------------- *)

(* The set of all non‑empty sequences of length 1..MaxSeqLen over Values *)
AllSeqs == { s \in Seq : Len(s) \in 1..MaxSeqLen }

(* An interval is a pair <<i,j>> with 1 <= i <= j <= Len(seq) *)
Interval == [i: Nat, j: Nat]
IntSet == { <<i, j>> \in [i : Nat, j : Nat] : i <= j }

(* Permutation of a sequence: exists a bijection on indices that reorders it *)
IsPerm(s, t) ==
  /\ Len(s) = Len(t)
  /\ \E f \in [1..Len(s) -> 1..Len(s)] :
        /\ \A x \in 1..Len(s) : \E y \in 1..Len(s) : f[x] = y
        /\ \A y \in 1..Len(s) : \E! x \in 1..Len(s) : f[x] = y
        /\ \A i \in 1..Len(s) : t[i] = s[f[i]]

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES seq, orig, work, pc

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ seq \in AllSeqs
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Running"

(* ----------------------------------------------------------------------
   Helper to compute the set of indices of an interval
   ---------------------------------------------------------------------- *)
Idxs(int) == { k \in 1..Len(seq) : int.i <= k /\ k <= int.j }

(* ----------------------------------------------------------------------
   Partition step (abstract)
   ---------------------------------------------------------------------- *)
Partition(seq, int, p) ==
  LET lo == int.i
      hi == int.j
      loSet == { k \in Idxs(int) : k <= p }
      hiSet == Idxs(int) \ loSet
      unchanged == seq \cup { i : i \in 1..Len(seq) : i \notin Idxs(int) }
   IN
    { s \in [1..Len(seq) -> Values] :
        /\ \A i \in 1..Len(seq) :
              (i \in Idxs(int) => s[i] \in Values)
              /\ (i \notin Idxs(int) => s[i] = seq[i])
        /\ \A i \in loSet, j \in hiSet : s[i] <= s[j] }

(* ----------------------------------------------------------------------
   The single-step action
   ---------------------------------------------------------------------- *)
Step ==
  \/ /\ pc = "Running"
        /\ work # {}
        /\ \E int \in work :
            CASE Len(seq) = 0 -> FALSE  \* safety, never true
            [] /\ int.i <= int.j
            [] /\ IF int.i = int.j
                THEN /\ work' = work \ {int}
                     /\ seq' = seq
                ELSE
                    /\ \E p \in int.i .. int.j :
                         /\ seq' \in Partition(seq, int, p)
                         /\ work' = (work \ {int}) \cup
                                    { <<int.i, p>>, <<p+1, int.j>>}
        /\ pc' = "Running"
        /\ orig' = orig
        /\ UNCHANGED <<orig, pc>>
  \/ /\ pc = "Running"
        /\ work = {}
        /\ pc' = "Done"
        /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
        /\ pc' = "Done"
        /\ UNCHANGED <<seq, orig, work>>

Next == Step

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(* ----------------------------------------------------------------------
   Safety invariants
   ---------------------------------------------------------------------- *)

(* Type correctness *)
TypeOK ==
  /\ seq \in [1..Len(seq) -> Values]
  /\ orig \in [1..Len(orig) -> Values]
  /\ work \subseteq { <<i, j>> \in IntSet : i <= j /\ j <= Len(seq) }
  /\ pc \in {"Running", "Done"}

(* Inductive invariant: permutation preserved *)
Inv == IsPerm(orig, seq)

(* Partial correctness: when done, seq is sorted and a permutation of orig *)
PCorrect ==
  /\ pc = "Done"
  /\ Inv
  /\ \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

(* ----------------------------------------------------------------------
   Liveness property (termination)
   ---------------------------------------------------------------------- *)
Termination == []<>(pc = "Done")

=============================================================================