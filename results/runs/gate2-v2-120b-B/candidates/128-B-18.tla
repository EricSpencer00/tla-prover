---- MODULE Quicksort
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* If you are not already familiar with that algorithm, you should look it *)
(* up on the Web and understand how it works--including what the partition *)
(* procedure does, without worrying about how it does it.  The version     *)
(* presented here does not specify a partition procedure, but chooses in a *)
(* single step an arbitrary value that is the result that any partition    *)
(* procedure may produce.                                                  *)
(*                                                                         *)
(* The module also has a structured informal proof of Quicksort's partial  *)
(* correctness property--namely, that if it terminates, it produces a      *)
(* sorted permutation of the original sequence.  As described in the note  *)
(* "Proving Safety Properties", the proof uses the TLAPS proof system to   *)
(* check the decomposition of the proof into substeps, and to check some   *)
(* of the substeps whose proofs are trivial.                               *)
(*                                                                         *)
(* The version of Quicksort described here sorts a finite sequence of      *)
(* integers.  It is one of the examples in Section 7.3 of "Proving Safety  *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

(***************************************************************************)
(* To aid in model checking the spec, we assume that the sequence to be    *)
(* sorted are elements of a set Values of integers.                        *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* PermsOf(s) is the set of all permutations of a sequence s.               *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN { s ** f : f \in Automorphisms(DOMAIN s) }

(***************************************************************************)
(* Max(S) and Min(S) are the maximum and minimum of a non‑empty finite set *)
(* S of integers.                                                          *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(***************************************************************************)
(* Partitions(I, p, s) is the set of all sequences that can result from a  *)
(* partition of interval I of s using pivot index p.                       *)
(***************************************************************************)
Partitions(I, p, s) ==
  { t \in PermsOf(s) :
        /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
        /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j]) }

(***************************************************************************)
(* UV is a convenient view of U that also contains the singleton intervals*)
(* for every position that is not currently covered by U.                   *)
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
  /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
  /\ pc \in {"a", "Done"}

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

(***************************************************************************)
(* The PlusCal algorithm, translated to TLA+.                               *)
(***************************************************************************)
VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"
  /\ seq0' = seq0   \* (keeps seq0 unchanged)

a ==
  /\ pc = "a"
  /\ IF U # {}
        THEN
          /\ \E I \in U :
               IF Cardinality(I) = 1
                 THEN /\ U' = U \ {I}
                      /\ seq' = seq
                 ELSE
                   /\ \E p \in Min(I)..(Max(I)-1) :
                         /\ \E newseq \in Partitions(I, p, seq) :
                               /\ seq' = newseq
                               /\ U' = (U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
          /\ pc' = "a"
        ELSE
          /\ pc' = "Done"
          /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0   \* seq0 never changes

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars

PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

=============================================================================