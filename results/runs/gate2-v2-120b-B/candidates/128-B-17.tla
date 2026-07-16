---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

\* Permutations of a sequence
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN { s ** f : f \in Automorphisms(DOMAIN s) }

\* Max and Min for non‑empty integer sets
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Allowed results of a partition on interval I with pivot p
Partitions(I, p, s) ==
  { t \in PermsOf(s) :
        /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
        /\ \A i, j \in I :
              (i <= p) /\ (p < j) => (t[i] <= t[j]) }

\* Variables
VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

\* Initial state
Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

\* Action a: the algorithm step
a ==
  IF U # {}
    THEN
      \E I \in U :
        IF Cardinality(I) = 1
          THEN /\ pc' = "a"
               /\ seq' = seq
               /\ U' = U \ {I}
          ELSE
            \E p \in Min(I) .. (Max(I) - 1) :
              LET I1 == Min(I)..p
                  I2 == (p+1)..Max(I) IN
                \E newseq \in Partitions(I, p, seq) :
                  /\ pc' = "a"
                  /\ seq' = newseq
                  /\ U' = (U \ {I}) \cup {I1, I2}
    ELSE /\ pc' = "Done"
         /\ UNCHANGED << seq, U >>
  /\ UNCHANGED seq0

\* Stuttering on termination
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars

\* Post‑condition invariant
PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

\* Type correctness (used in the inductive invariant)
TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
  /\ pc \in {"a", "Done"}

\* UV: the set of intervals currently “covered” plus singletons for any index
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}}

\* UV must be a proper partition of 1..Len(seq0)
DomainPartitions ==
  { DP \in SUBSET (SUBSET (1..Len(seq0))) :
        /\ (UNION DP) = 1..Len(seq0)
        /\ \A I \in DP : I = Min(I)..Max(I)
        /\ \A I, J \in DP : I # J => I \cap J = {} }

\* Order condition between two intervals
RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

\* The inductive invariant
Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : I # J => RelSorted(I, J)

=============================================================================