---- MODULE Quicksort ---------------------------------------------------------
(* A Quicksort-like sorting algorithm over a finite sequence of integers.   *)
(* The algorithm maintains a set of subintervals of the sequence that still  *)
(* need sorting; it repeatedly picks one, and if it has more than one       *)
(* element, it "partitions" it by replacing it with a permutation that       *)
(* respects the pivot order.  The TLAPS proof below shows that the algorithm  *)
(* is safe: whenever it stops, the sequence is a sorted permutation of the   *)
(* original.                                                                 *)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(**************************************************************************)
(* Permutations of a sequence: compose it with any permutation of its        *)
(* domain (1..Len(s)).                                                     *)
(**************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(**************************************************************************)
(* The result of partitioning interval I with pivot p: any permutation of   *)
(* seq that leaves indices outside I alone and orders I so that the p-th    *)
(* element separates the low values from the high ones.                     *)
(**************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) : /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
                       /\ \A i \in I, j \in I : (i <= p /\ p < j) => (t[i] <= t[j])}

DomainPartitions ==
  {DP \in SUBSET (SUBSET (1..Len(seq0))) :
       /\ UNION DP = 1..Len(seq0)
       /\ \A I \in DP : I = Min(I)..Max(I)
       /\ \A I, J \in DP : (I # J) => I \cap J = {}}

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET (SUBSET (1..Len(seq0)) \ {{}})
  /\ pc \in {"a", "Done"}

\* UV adds a singleton set for every index not covered by U.
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

a ==
  LET I1(p) == Min(I)..p
      I2(p) == (p+1)..Max(I)
  IN
  /\ pc = "a"
  /\ IF U = {}
       THEN /\ pc' = "Done"
            /\ UNCHANGED << seq, seq0, U >>
       ELSE /\ \E I \in U :
              /\ IF Cardinality(I) = 1
                   THEN /\ U' = U \ {I}
                        /\ seq' = seq
                   ELSE /\ \E p \in Min(I)..(Max(I)-1) :
                           /\ seq' \in Partitions(I, p, seq)
                           /\ U' = (U \ {I}) \cup {I1(p), I2(p)}
              /\ pc' = "a"
            /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a)

Termination == <>(pc = "Done")

PCorrect == (pc = "Done") => /\ seq \in PermsOf(seq0)
                                  /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

=============================================================================