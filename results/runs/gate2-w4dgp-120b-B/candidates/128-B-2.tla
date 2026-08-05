---- MODULE Quicksort ----
(* Quicksort as an abstract nondeterministic algorithm that moves one
   interval at a time through a set of intervals being partitioned into
   disjoint subintervals, where the partition step is given abstraction
   freedom but keeps the partitioned interval's values in sorted order
   relative to the two halves.  Its termination invariant and the
   partial-correctness postcondition proved from it are both in the
   module.  From "Proving Safety Properties". *)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \subseteq (SUBSET (1..Len(seq0))) \ {{}} /\ pc \in {"a", "Done"}

\* UV is the set of intervals that are either in U or collapsed to a
\* singleton; it is invariantly a partition of 1..Len(seq0), where the
\* interval ordering relativizes seq's sortedness.
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}
DomainPartitions ==
  {DP \subseteq SUBSET (1..Len(seq0)) :
      /\ (UNION DP) = 1..Len(seq0)
      /\ \A I \in DP : I = Min(I)..Max(I)
      /\ \A I, J \in DP : (I # J) => (I \cap J = {})}

PermsOf(s) ==
  LET Auto(S) == {f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y}
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN {s ** f : f \in Auto(DOMAIN s)}

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

Init == /\ seq \in Seq(Values) \ {<<>>}
        /\ seq0 = seq
        /\ U = {1..Len(seq)}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF U # {}
          THEN /\ \E I \in U :
                  (Cardinality(I) = 1) =>
                    /\ U' = U \ {I}
                    /\ seq' = seq
                  /\ (Cardinality(I) # 1) =>
                    /\ \E p \in Min(I) .. (Max(I)-1) :
                         LET I1 == Min(I)..p IN
                         LET I2 == (p+1)..Max(I) IN
                         /\ \E newseq \in {t \in PermsOf(seq) :
                                            /\ \A i \in (1..Len(seq)) \ I : t[i] = seq[i]
                                            /\ \A i \in I1, j \in I2 : t[i] =< t[j]}
                              /\ seq' = newseq
                              /\ U' = ((U \ {I}) \cup {I1, I2})
          /\ pc' = "a"
          /\ UNCHANGED seq0
          /\ UNCHANGED UV
          /\ UNCHANGED DomainPartitions
          /\ UNCHANGED RelSorted
          /\ UNCHANGED PermsOf
     ELSE /\ pc' = "Done" /\ UNCHANGED <<seq, U, seq0>>

Next == a

Spec == Init /\ [][Next]_<<seq, U, pc, seq0>>

Terminating == <>(pc = "Done")
PCorrect == (pc = "Done") => /\ seq \in PermsOf(seq0)
                               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

Inv == /\ TypeOK
        /\ (pc = "Done") => (U = {})
        /\ UV \in DomainPartitions
        /\ seq \in PermsOf(seq0)
        /\ UNION UV = 1..Len(seq0)
        /\ \A I, J \in UV : (I # J) => RelSorted(I, J)
====