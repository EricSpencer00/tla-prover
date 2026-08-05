---- MODULE Quicksort ----
(* Quicksort: an abstract version with a non-deterministic partition step.
   The sorted subintervals are merged into a set U of intervals to be
   partitioned; the set UV of nonempty subintervals covered by a partitioned
   interval is tracked as an invariant, and the postcondition is that the
   result is a sorted permutation of the original sequence.  The proof
   follows the step-indexed style of "Proving Safety Properties". *)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME Values \subseteq Int

PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j])}

VARIABLES seq, seq0, U, pc
vars == << seq, seq0, U, pc >>

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
  /\ pc \in {"a", "Done"}

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions ==
  {DP \in SUBSET SUBSET (1..Len(seq0)) :
      /\ (UNION DP) = 1..Len(seq0)
      /\ \A I \in DP : I = Min(I)..Max(I)
      /\ \A I, J \in DP : (I # J) => (I \cap J = {})}

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

a ==
  /\ pc = "a"
  /\ IF U # {}
       THEN /\ \E I \in U :
              IF Cardinality(I) = 1
                THEN /\ U' = U \ {I}
                     /\ seq' = seq
                ELSE /\ \E p \in Min(I)..(Max(I)-1) :
                        LET I1 == Min(I)..p IN
                          LET I2 == (p+1)..Max(I) IN
                            \E newseq \in Partitions(I, p, seq) :
                              /\ seq' = newseq
                              /\ U' = ((U \ {I}) \cup {I1, I2})
                     /\ UNCHANGED seq0
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << seq, seq0, U >>
  /\ UNCHANGED pc

Next == a

Spec == Init /\ [][Next]_vars

PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

(* The sorted-interval set UV is not the same as U, so preventing U from
   growing is insufficient; the invariant tracks the whole set of sorted
   subintervals covered by any partitioned interval.  The level-<1> steps
   below can be checked by TLC with sequences of length at most 3. *)
Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2>1. Init => TypeOK /\ UV \in DomainPartitions /\ seq \in PermsOf(seq0)
        /\ UNION UV = 1..Len(seq0) /\ \A I, J \in UV : (I # J) => RelSorted(I, J)
    BY DEF Init, UV, PermsOf, DomainPartitions, RelSorted
  <2>2. QED
    BY <2>1, Defs
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. Inv /\ [Next]_vars => Inv'
    BY DEF Next, Inv
  <2>2. QED
    BY <2>1, Defs
<1>3. Inv => PCorrect
  <2>1. Inv => (pc = "Done") => (seq \in PermsOf(seq0) /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q])
    BY DEF PCorrect, Inv
  <2>2. QED
    BY <2>1, DEF
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL
====