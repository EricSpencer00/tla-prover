---- MODULE Quicksort
(* This module contains an abstract version of the Quicksort algorithm. *)
(* If you are not already familiar with that algorithm, you should look it *)
(* up on the Web and understand how it works--including what the partition  *)
(* procedure does, without worrying about how it does it.  The version here  *)
(* does not specify a partition procedure, but chooses in a single step an  *)
(* arbitrary value that is the result any partition procedure may produce.  *)
(*                                                                        *)
(* The module also has a structured informal proof of Quicksort's partial *)
(* correctness property--namely, that if it terminates, it produces a       *)
(* sorted permutation of the original sequence.  As described in the note   *)
(* "Proving Safety Properties", the proof uses the TLAPS proof system to    *)
(* check the decomposition into substeps, and to check some substeps whose  *)
(* proofs are trivial.                                                     *)
(*                                                                        *)
(* The module sorts a finite sequence of integers.  It is one of the       *)
(* examples in Section 7.3 of "Proving Safety Properties" at              *)
(* https://lamport.azurewebsites.net/tla/proving-safety.pdf                *)

EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(* PermsOf(s) is the set of permutations of a sequence s of integers: all   *)
(* compositions of s with a permutation of its domain.  Automorphisms(S) is  *)
(* the set of all permutations of a finite set S.                           *)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(* Partitions(I, p, s) is the set of all new values of s that a partition  *)
(* may produce for the subinterval I using the pivot index p: the values     *)
(* outside I are unchanged and those inside I are permuted so that the      *)
(* values up to p are <= the values after p.                               *)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j])}

DomainPartitions == {DP \in SUBSET SUBSET (1..Len(seq0)) :
                      /\ (UNION DP) = 1..Len(seq0)
                      /\ \A I \in DP : I = Min(I)..Max(I)
                      /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
          /\ pc \in {"a", "Done"}

(* UV is the set of intervals in the current partitioning, plus all the   *)
(* singletons of elements not currently in an interval.                    *)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

\* The algorithm repeatedly picks an interval in U and partitions it,       *)
(* unless it is a singleton, in which case it is simply removed.
\* BEGIN TRANSLATION
VARIABLES seq, seq0, U, pc
vars == << seq, seq0, U, pc >>

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

a ==
  /\ pc = "a"
  /\ IF U # {}
       THEN /\ \E I \in U : a!2!2!1!(I)
              /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == a \/ Terminating
Spec == Init /\ [][Next]_vars
        /\ WF_vars(a)

Termination == <>(pc = "Done")

(* When the algorithm terminates, seq is a sorted permutation of seq0.    *)
PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

Inv == /\ TypeOK
       /\ (pc = "Done") => (U = {})
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  OBVIOUS
<1>2. Inv /\ [Next]_vars => Inv'
  OBVIOUS
<1>3. Inv => PCorrect
  OBVIOUS

=============================================================================