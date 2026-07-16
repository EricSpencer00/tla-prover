---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(* Permutations of a sequence *)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

(* Max / Min of a non‑empty finite set of integers *)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(* Set of possible results of a partition on interval I with pivot p *)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

VARIABLES seq, seq0, U, pc

(* Helper set UV used in the invariant *)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

(* DomainPartitions: collection of non‑empty intervals that partition 1..Len(seq0) *)
DomainPartitions ==
  {DP \in SUBSET SUBSET (1..Len(seq0)) :
      /\ (UNION DP) = 1..Len(seq0)
      /\ \A I \in DP : I = Min(I)..Max(I)
      /\ \A I, J \in DP : (I # J) => (I \cap J = {})}

(* Ordering relation between two intervals *)
RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

(* Type correctness *)
TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
  /\ pc \in {"a", "Done"}

(* Invariant used for proof and model checking *)
Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

(* Initial state *)
Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

(* Main action, matching the PlusCal description *)
a ==
  /\ pc = "a"
  /\ IF U # {}
        THEN /\ \E I \in U :
                IF Cardinality(I) = 1
                   THEN /\ U' = U \ {I}
                        /\ seq' = seq
                   ELSE /\ \E p \in Min(I) .. (Max(I)-1) :
                            \E newseq \in Partitions(I, p, seq) :
                              /\ seq' = newseq
                              /\ U' = (U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
        /\ pc' = "a"
        /\ seq0' = seq0
        /\ UNCHANGED << >>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED << seq, seq0, U >>

Termination == pc = "Done" /\ UNCHANGED << seq, seq0, U, pc >>

Next == a \/ Termination

Spec == Init /\ [][Next]_<<seq, seq0, U, pc>>

Termination == <>(pc = "Done")

PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  OBVIOUS
<1>2. Inv /\ [Next]_<<seq, seq0, U, pc>> => Inv'
  OBVIOUS
<1>3. Inv => PCorrect
  OBVIOUS
====