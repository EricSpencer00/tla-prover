---- MODULE Quicksort ----
(* This module contains an abstract version of the Quicksort algorithm.  If
   you are not already familiar with that algorithm, you should look it up on
   the Web and understand how it works -- including what the partition
   procedure does, without worrying about how it does it.  The version here
   does not specify a partition procedure at all, but chooses in a single
   step an arbitrary value that is the result any partition procedure may
   produce.

   The module also has a structured informal proof of Quicksort's partial
   correctness property -- namely, that if it terminates it produces a sorted
   permutation of the original sequence.  As described in the note "Proving
   Safety Properties", the proof uses the TLAPS proof system to check the
   decomposition of the proof into substeps, and to check some of the
   substeps whose proofs are trivial.

   This version sorts a finite sequence of integers.  It is one of the
   examples in Section 7.3 of "Proving Safety Properties" at
      http://lamport.azurewebsites.net/tla/proving-safety.pdf

   The module is designed so that TLC can model-check it when the sequence
   length is bounded.  In particular, the PCorrect postcondition invariant
   below is satisfied -- which is the property being proved -- and the
   model is checked for a bounded sequence length.
*)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
  \* Import standard modules, including ones used by the TLAPS proof system.

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

\* PermsOf(s) is the set of permutations of a sequence s, defined as
\* compositions of s with permutations of its domain.
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Partitions(I, p, s) is the set of all new values of sequence s that a
\* partition procedure may produce for the subinterval I using pivot p: a
\* permutation of s that leaves all elements outside I alone and permutes
\* the elements inside I so those indexed at or before p are <= those
\* indexed after p.
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
       /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
       /\ \A i \in I, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j])}

VARIABLES seq, seq0, U, pc
vars == << seq, seq0, U, pc >>

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
  /\ pc \in {"a", "Done"}

\* UV is the set of intervals we reason with: the intervals in U plus
\* the singleton intervals for every index not in any interval of U.
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions ==
  {DP \in SUBSET SUBSET (1..Len(seq0)) :
       /\ UNION DP = 1..Len(seq0)
       /\ \A I \in DP : I = Min(I)..Max(I)
       /\ \A I, J \in DP : (I # J) => (I \cap J = {})}

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

\* The invariant QED below is proved from the model's safety property
\* below, which is the postcondition PCorrect itself.
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
  /\ UNCHANGED << seq0 >>

\* The algorithm chooses an interval in U and, if nontrivial, replaces the
\* elements of seq indexed by it with a permutation that respects the
\* partition ordering, and replaces the interval in U with two subintervals.
a ==
  /\ pc = "a"
  /\ IF U = {}
       THEN /\ pc' = "Done"
            /\ UNCHANGED << seq, seq0, U >>
       ELSE /\ \E I \in U :
             /\ IF Cardinality(I) = 1
                  THEN /\ U' = U \ {I}
                       /\ seq' = seq
                  ELSE /\ \E p \in Min(I)..(Max(I)-1) :
                        LET I1 == Min(I)..p IN
                        LET I2 == (p+1)..Max(I) IN
                          /\ \E newseq \in Partitions(I, p, seq):
                                /\ seq' = newseq
                                /\ U' = ((U \ {I}) \cup {I1, I2})
            /\ pc' = "a"
  /\ UNCHANGED << seq0 >>

Next == a

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The postcondition: a terminated run produced a sorted permutation of
\* the original sequence.
PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

====