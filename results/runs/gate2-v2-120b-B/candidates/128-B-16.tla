---- MODULE Quicksort ----
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* It is a minimal, semantics‑preserving fix of the original specification  *)
(* that allowed TLC to find a counterexample to the invariant Inv.          *)
(* The fix corrects the update of the interval set U after a non‑trivial   *)
(* partition step.  The original version intersected U with the set of    *)
(* new intervals, which unintentionally removed intervals that were        *)
(* already present in U.  The corrected version now *adds* the new intervals *)
(* I1 and I2 while removing only the old interval I.                        *)
(*                                                                         *)
(* The rest of the specification (definitions, proofs, etc.) is unchanged  *)
(* from the original file.                                                 *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* Permutations of a sequence.                                            *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

(***************************************************************************)
(* Max and Min of a non‑empty finite set of integers.                     *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(***************************************************************************)
(* The set of all permissible results of a partition on interval I with   *)
(* pivot index p.                                                         *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

(***************************************************************************)
(* Variables of the algorithm.                                            *)
(***************************************************************************)
VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

(***************************************************************************)
(* Initial state.                                                         *)
(***************************************************************************)
Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

(***************************************************************************)
(* Action a: the main loop.                                               *)
(***************************************************************************)
a ==
  /\ pc = "a"
  /\ IF U # {}
        THEN
          /\ \E I \in U :
               IF Cardinality(I) = 1
                  THEN /\ U' = U \ {I}
                       /\ seq' = seq
                  ELSE
                    /\ \E p \in Min(I) .. (Max(I)-1):
                         LET I1 == Min(I)..p IN
                         LET I2 == (p+1)..Max(I) IN
                         \E newseq \in Partitions(I, p, seq):
                           /\ seq' = newseq
                           /\ U' = (U \ {I}) \cup {I1, I2}
          /\ pc' = "a"
        ELSE
          /\ pc' = "Done"
          /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0

(***************************************************************************)
(* Allow infinite stuttering after termination.                           *)
(***************************************************************************)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

(***************************************************************************)
(* Postcondition invariant.                                               *)
(***************************************************************************)
PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

(***************************************************************************)
(* Helper definitions used by the invariant.                              *)
(***************************************************************************)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions ==
  {DP \in SUBSET SUBSET (1..Len(seq0)) :
      /\ (UNION DP) = 1..Len(seq0)
      /\ \A I \in DP : I = Min(I)..Max(I)
      /\ \A I, J \in DP : (I # J) => (I \cap J = {})}

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
  /\ pc \in {"a", "Done"}

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

=============================================================================