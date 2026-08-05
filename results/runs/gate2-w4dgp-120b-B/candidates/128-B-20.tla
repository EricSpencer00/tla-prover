---- MODULE Quicksort
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* It is a correct but nondeterministic implementation and comes with an    *)
(* informal proof of its partial correctness.  The formal part below does  *)
(* not model a realistic partition procedure: a partition step nondetermin-*)
(* istically picks any result that any partition could have produced.      *)
(*                                                                          *)
(* The postcondition proved here is partial correctness: termination     *)
(* implies a sorted permutation of the original sequence.  TLAPS is used to  *)
(* check the structural proof.                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

Values == {0, 1, 2}
ASSUME Values \subseteq Int

\* Permutations of a sequence s : compose s with a domain permutation.
PermsOf(s) ==
  LET Perms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Perms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* What a partition step is allowed to produce for interval I with pivot p.
Partitions(I, p, s) ==
  { t \in PermsOf(s) :
       /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
       /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j]) }

\* seq : the array; seq0 : the original value; U : subintervals to sort.
VARIABLES seq, seq0, U, pc
vars == << seq, seq0, U, pc >>

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

a ==
  /\ pc = "a"
  /\ IF U = {}
       THEN pc' = "Done"
       ELSE \E I \in U, p \in Min(I)..(Max(I)-1), newseq \in Partitions(I, p, seq) :
              /\ seq' = newseq
              /\ U' = ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)})
              /\ pc' = "a"
  /\ seq0' = seq0

Next == a

TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \subseteq (SUBSET (1..Len(seq0))) \ {{}} 
          /\ pc \in {"a", "Done"}

\* UV keeps the interval set UV closed under singleton refinement.
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions == {DP \subseteq SUBSET (1..Len(seq0)) :
    /\ (UNION DP) = 1..Len(seq0)
    /\ \A I \in DP : I = Min(I)..Max(I)
    /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

Spec == Init /\ [][a]_vars

PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

FAIRNESS a

====