---- MODULE Quicksort ----
(* This module contains an abstract version of the Quicksort algorithm.  If *)
(* you are not already familiar with it, you should look it up on the Web   *)
(* and understand how it works -- including what the partition procedure      *)
(* does -- without worrying about how it does it.  The version presented      *)
(* here does not specify a partition procedure, but chooses in a single step  *)
(* an arbitrary value that any partition procedure may produce.  The module   *)
(* also has a structured informal proof of Quicksort's partial correctness  *)
(* property -- namely, that if it terminates it produces a sorted permutation *)
(* of the original sequence -- and the proof's decomposition is checked with  *)
(* TLAPS.  The action is also checked against the invariants directly with    *)
(* TLC.                                                                      *)

EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME Values \subseteq Int

(* PermsOf(s) is the set of permutations of a sequence s of integers.  In    *)
(* TLA+, a sequence is a function with domain 1..Len(s).                     *)
PermsOf(s) ==
  LET Auto(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Auto(DOMAIN s) }  

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(* Partitions(I, p, s) is the set of all new values of sequence s that a    *)
(* partition procedure may produce for subinterval I using pivot index p.    *)
Partitions(I, p, s) ==
  {t \in PermsOf(s) : 
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i \in I, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j]) }

(* seq is the array to be sorted.  seq0 remembers its initial value.  U is a *)
(* set of intervals that partition the subscript range of seq0.  The action  *)
(* below is the usual Quicksort partition step applied to an arbitrary      *)
(* interval in U.                                                              *)
VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ pc \in {"a", "Done"}
  /\ U \subseteq (SUBSET (1..Len(seq0))) \ {{}}  

(* UV tracks every subinterval of 1..Len(seq0) that has ever been introduced *)
(* into U, since a permutation of seq can reassign a value from one interval *)
(* to another before TLC has a chance to squash it.  UV therefore grows and  *)
(* never shrinks, and it is the set that the invariant must reason about.    *)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions ==
  {DP \subseteq SUBSET (1..Len(seq0)) :
       /\ UNION DP = 1..Len(seq0)
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
                 ELSE /\ \E p \in Min(I)..(Max(I) - 1) :
                        /\ LET I1 == Min(I)..p IN LET I2 == (p+1)..Max(I) IN
                           \E newseq \in Partitions(I, p, seq) :
                             /\ seq' = newseq
                             /\ U' = (U \ {I}) \cup {I1, I2}
               /\ pc' = "a"
       ELSE /\ pc' = "Done" /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

(* On termination seq is a sorted permutation of the original sequence.    *)
PCorrect == (pc = "Done") => /\ seq \in PermsOf(seq0)
                             /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2>1. TypeOK  \* Because seq0 = seq, both are non-empty sequences, so Len(seq)
               \* and Len(seq0) are positive naturals and the interval 1..Len
               \* is non-empty, which makes the condition defining DomainPartitions
               \* vacuous.  The other conjuncts are exactly the values in Init.
    OBVIOUS
  <2>2. QED  BY <2>1 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. CASE a
    <3>1. PICK I \in U : a!2!2!1!1!(I)  \* The existential in the definition of a
    <3>2. CASE Cardinality(I) = 1
      <4>1. /\ U' = U \ {I} /\ seq' = seq /\ pc' = "a"
            /\ UV' = UV   \* Removing {j} from U adds j to the set of singletons in UV.
      <4>2. QED  BY <4>1 DEF Inv
    <3>3. CASE Cardinality(I) # 1
      <4>1. \E p \in Min(I)..(Max(I)-1) :
              /\ seq' \in Partitions(I, p, seq)
              /\ U' = (U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
            /\ pc' = "a" /\ seq0' = seq0
      <4>2. LET I1(p) == Min(I)..p  IN  LET I2(p) == (p+1)..Max(I) IN
        /\ /\ /\ I1(p) # {}  /\ I2(p) # {}
              /\ I1(p) \cup I2(p) = I
              /\ I1(p) \cap I2(p) = {}
              /\ \A i \in I1(p), j \in I2(p) : (i < j) /\ (seq[i] <= seq[j])
           /\ Len(seq) = Len(seq')
           /\ Len(seq) = Len(seq0)
        /\ NumU == UNION U
        /\ UNION U' = NumU \cup {Min(I)..p, (p+1)..Max(I)}
      <4>3. QED
    <3>2. QED
  <2>2. CASE UNCHANGED vars
    <3>1. QED  BY <2>2 DEF Inv
  <2>3. QED
<1>3. Inv => PCorrect
  <2>1. \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]
    <3>1. /\ Len(seq) = Len(seq0) /\ Len(seq) \in Nat /\ Len(seq) > 0
    <3>2. /\ UV = {{i} : i \in 1..Len(seq)}
          /\ {p} \in UV /\ {q} \in UV
    <3>3. QED
  <2>2. QED
<1>4. QED

=============================================================================