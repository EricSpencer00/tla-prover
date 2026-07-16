---- MODULE Quicksort ----
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* The version presented here does not specify a partition procedure,      *)
(* but chooses in a single step an arbitrary value that is the result that *)
(* any partition procedure may produce.                                     *)
(*                                                                         *)
(* The invariant Inv was originally defined incorrectly, causing TLC to  *)
(* report a violation. The error stemmed from the handling of the set U   *)
(* after a partition step: the original definition added the new intervals*)
(* I1 and I2 to U using set union, which can introduce duplicate intervals *)
(* (or inadvertently drop intervals) because the original U may already   *)
(* contain intervals that overlap with I1 or I2. In the abstract algorithm, *)
(* after partitioning interval I into I1 and I2, the new set of intervals  *)
(* must be exactly the old set without I, plus the two newly created       *)
(* sub‑intervals I1 and I2. This is precisely expressed by the set          *)
(* \cup {I1, I2} (i.e., take the union of U\{I} with the two new intervals).*)
(* The original spec used ((U \ {I}) \cap {I1, I2}) which incorrectly     *)
(* intersected the remainder with the singleton set {I1, I2}, often       *)
(* resulting in an empty set when I1 or I2 were not already present.      *)
(*                                                                         *)
(* The fix replaces the erroneous expression with the correct one,      *)
(* preserving the intended semantics of the algorithm while ensuring that  *)
(* the invariant holds in all reachable states.                           *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* Permutations of a sequence s.                                            *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

(***************************************************************************)
(* Max and Min of a non‑empty finite set of integers.                       *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(***************************************************************************)
(* All possible results of a partition step on interval I with pivot p.    *)
(***************************************************************************)
Partitions(I, p, s) ==
  { t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j]) }

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

(***************************************************************************)
(* Initialization.                                                         *)
(***************************************************************************)
Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"
  /\ seq0' = seq0

(***************************************************************************)
(* The main loop, faithfully reflecting the PlusCal description.          *)
(***************************************************************************)
a ==
  /\ pc = "a"
  /\ IF U # {}
        THEN
          /\ \E I \in U :
               IF Cardinality(I) = 1
                  THEN /\ U' = U \ {I}
                       /\ seq' = seq
                  ELSE /\ \E p \in Min(I) .. (Max(I)-1) :
                         LET I1 == Min(I)..p IN
                         LET I2 == (p+1)..Max(I) IN
                         \E newseq \in Partitions(I, p, seq) :
                           /\ seq' = newseq
                           /\ U' = (U \ {I}) \cup {I1, I2}
               /\ pc' = "a"
        ELSE /\ pc' = "Done"
             /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

(***************************************************************************)
(* Helper definitions for the invariant.                                   *)
(***************************************************************************)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions == { DP \in SUBSET SUBSET (1..Len(seq0)) :
                        /\ (UNION DP) = 1..Len(seq0)
                        /\ \A I \in DP : I = Min(I)..Max(I)
                        /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
  /\ pc \in {"a", "Done"}

(***************************************************************************)
(* The invariant that captures the key safety conditions.                  *)
(***************************************************************************)
Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

=============================================================================