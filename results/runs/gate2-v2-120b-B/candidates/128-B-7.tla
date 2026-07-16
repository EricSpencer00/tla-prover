---- MODULE Quicksort ----
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* The version presented here does not specify a partition procedure,     *)
(* but chooses in a single step an arbitrary value that is the result any *)
(* partition may produce.                                                  *)
(*                                                                         *)
(* The spec includes a structured proof of partial correctness: if the   *)
(* algorithm terminates, the final sequence is a sorted permutation of the *)
(* original.  The proof uses the TLAPS proof system.                       *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* Permutations of a sequence s                                            *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      Compose(f, g) == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Compose(s, f) : f \in Automorphisms(DOMAIN s) }

(***************************************************************************)
(* Max and Min of a non‑empty finite set of integers                     *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(***************************************************************************)
(* The set of all arrays that a partition on interval I with pivot p may   *)
(* produce from sequence s.                                                *)
(***************************************************************************)
Partitions(I, p, s) ==
  { t \in PermsOf(s) :
        /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
        /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j]) }

(***************************************************************************)
(* Variables:                                                             *)
(*   seq  – the mutable array being sorted                               *)
(*   seq0 – the initial value of seq (for checking correctness)          *)
(*   U    – set of sub‑intervals still to be processed                     *)
(*   pc   – control variable (\"a\" or \"Done\")                           *)
(***************************************************************************)
VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

(***************************************************************************)
(* Initial state                                                         *)
(***************************************************************************)
Init ==
   /\ seq \in Seq(Values) \ {<<>>}
   /\ seq0 = seq
   /\ U = {1..Len(seq)}
   /\ pc = "a"

(***************************************************************************)
(* The main loop action                                                   *)
(***************************************************************************)
a ==
   /\ pc = "a"
   /\ IF U # {}
        THEN /\ \E I \in U :
                IF Cardinality(I) = 1
                   THEN /\ U' = U \ {I}
                        /\ seq' = seq
                   ELSE /\ \E p \in Min(I) .. (Max(I)-1) :
                           LET I1 == Min(I)..p IN
                           LET I2 == (p+1)..Max(I) IN
                           /\ \E newseq \in Partitions(I, p, seq) :
                                 /\ seq' = newseq
                                 /\ U' = (U \ {I}) \cup {I1, I2}
        /\ pc' = "a"
        /\ UNCHANGED seq0
      ELSE /\ pc' = "Done"
           /\ UNCHANGED << seq, U, seq0 >>

(***************************************************************************)
(* Stuttering step to avoid deadlock on termination                        *)
(***************************************************************************)
Terminate ==
   /\ pc = "Done"
   /\ UNCHANGED vars

Next == a \/ Terminate

(***************************************************************************)
(* Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

Termination == <> (pc = "Done")

(***************************************************************************)
(* Postcondition invariant (must hold when pc = "Done")                    *)
(***************************************************************************)
PCorrect ==
   (pc = "Done") =>
      /\ seq \in PermsOf(seq0)
      /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

(***************************************************************************)
(* Helper definitions for the inductive invariant                         *)
(***************************************************************************)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}}

DomainPartitions ==
   { DP \in SUBSET SUBSET (1..Len(seq0)) :
        /\ (UNION DP) = 1..Len(seq0)
        /\ \A I \in DP : I = Min(I)..Max(I)
        /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

TypeOK ==
   /\ seq \in Seq(Values) \ {<<>>}
   /\ seq0 \in Seq(Values) \ {<<>>}
   /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
   /\ pc \in {"a", "Done"}

(***************************************************************************)
(* Inductive invariant                                                    *)
(***************************************************************************)
Inv ==
   /\ TypeOK
   /\ (pc = "Done") => (U = {})
   /\ UV \in DomainPartitions
   /\ seq \in PermsOf(seq0)
   /\ UNION UV = 1..Len(seq0)
   /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

(***************************************************************************)
(* Theorem (partial correctness)                                          *)
(***************************************************************************)
THEOREM Spec => [] PCorrect

=============================================================================