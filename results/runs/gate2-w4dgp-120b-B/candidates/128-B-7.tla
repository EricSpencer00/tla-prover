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
(* The module sorts a finite sequence of values taken from the set Values. *)
(* The proof of partial correctness is expressed as a semantic             *)
(* invariant; the system is model-checked against it.                       *)
(*                                                                         *)
(* The version of Quicksort described here is one of the examples in       *)
(* Section 7.3 of "Proving Safety Properties", which is at                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

(***************************************************************************)
(* Values is the set of values that appear in the sequence to be sorted.   *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* PermsOf(s) is the set of all permutations of the sequence s.  A        *)
(* permutation of s is the composition of s with a permutation of its       *)
(* domain (the indices of s).                                              *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(***************************************************************************)
(* Partitions(I, p, s) is the set of all arrays that a partition          *)
(* procedure may produce for the subinterval I of s when it chooses p as    *)
(* its pivot index: the entries outside I are unchanged, and the entries   *)
(* inside I are permuted so that those with index <= p are <= those with   *)
(* index > p.                                                               *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
       /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
       /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j])}

DomainPartitions == {DP \in SUBSET SUBSET (1..Len(seq0)) :
  /\ (UNION DP) = 1..Len(seq0)
  /\ \A I \in DP : I = Min(I)..Max(I)
  /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

VARIABLES seq, seq0, U, pc

vars == <<seq, seq0, U, pc>>

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
  /\ pc \in {"a", "Done"}

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
               ELSE /\ \E p \in Min(I)..(Max(I)-1):
                     LET I1 == Min(I)..p IN
                       LET I2 == (p+1)..Max(I) IN
                         \E newseq \in Partitions(I, p, seq):
                           /\ seq' = newseq
                           /\ U' = ((U \ {I}) \cup {I1, I2})
             /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<seq, U>>
  /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* PCorrect is the partial-correctness postcondition: a sorted            *)
(* permutation of the original sequence, in every state where the system    *)
(* has halted.  The model checker checks it against the full state graph.   *)
(***************************************************************************)
PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

THEOREM Spec => []Inv /\ []PCorrect
<1>1. Init => Inv
  <2>1. TypeOK
    <3>1. seq \in Seq(Values) \ {<<>>} /\ seq0 \in Seq(Values) \ {<<>>}
      BY DEF Init
    <3>2. U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
      BY DEF Init
    <3>3. pc \in {"a", "Done"}
      BY DEF Init
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF TypeOK
  <2>2. UV \in DomainPartitions
    <3>1. UV = {1..Len(seq0)}
      BY DEF Init, UV
    <3>2. UV \in SUBSET SUBSET (1..Len(seq0))
      BY <3>1
    <3>3. (UNION UV) = 1..Len(seq0)
      BY <3>1
    <3>4. \A I, J \in UV : I = J
      BY <3>1
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF DomainPartitions
  <2>3. seq \in PermsOf(seq0)
    <3>1. seq \in PermsOf(seq)
      BY DEF Init
    <3>2. QED
      BY <3>1
  <2>4. UNION UV = 1..Len(seq0)
    BY DEF Init
  <2>5. \A I, J \in UV : (I # J) => RelSorted(I, J)
    BY DEF Init
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv

<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. CASE a
    <3>1. CASE U # {}
      <4>1. /\ pc = "a" /\ pc' = "a"
      <4>2. PICK I \in U : a!2!2!1!(I)
      <4>3. CASE Cardinality(I) = 1
        <5>1. /\ U' = U \ {I} /\ seq' = seq /\ seq0' = seq0
        <5>2. QED
          <6>1. UV' = UV
            BY <4>2, <4>3, <5>1
          <6>2. TypeOK'
            BY <4>1, <4>3, <5>1 DEF Inv, TypeOK
          <6>3. ((pc = "Done") => (U = {}))'
            BY <4>1, <4>3, <5>1 DEF Inv, TypeOK
          <6>4. (UV \in DomainPartitions)'
            BY <4>1, <4>3, <5>1 <6>1 DEF Inv
          <6>5. (seq \in PermsOf(seq0))'
            BY <4>1, <4>3, <5>1 DEF Inv
          <6>6. (UNION UV = 1..Len(seq0))'
            BY <5>1 <6>1 DEF Inv
          <6>7. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
            BY <4>1, <4>3, <5>1 <6>1 DEF Inv
          <6>8. QED
            BY <6>2, <6>3, <6>4, <6>5, <6>6, <6>7 DEF Inv
      <4>4. CASE Cardinality(I) # 1
        <5>1. seq0' = seq0
          BY DEF a
        <5> DEFINE I1(p) == Min(I)..p
                   I2(p) == (p+1)..Max(I)
        <5>2. PICK p \in Min(I)..(Max(I)-1) :
                /\ seq' \in Partitions(I, p, seq)
                /\ U' = ((U \ {I}) \cup {I1(p), I2(p)})
          BY <4>2, <4>4
        <5>3. /\ /\ I1(p) # {} /\ I1(p) = Min(I1(p))..Max(I1(p))
              /\ I1(p) \subseteq 1..Len(seq0)
              /\ /\ I2(p) # {} /\ I2(p) = Min(I2(p))..Max(I2(p))
                 /\ I2(p) \subseteq 1..Len(seq0)
              /\ I1(p) \cap I2(p) = {}
              /\ I1(p) \cup I2(p) = I
              /\ \A i \in I1(p), j \in I2(p) : (i < j) /\ (seq[i] <= seq[j])
          BY <5>2
        <5>4. /\ Len(seq) = Len(seq')
              /\ Len(seq) = Len(seq0)
          BY <5>2
        <5>5. UNION U = UNION U'
          BY <5>2, <5>3
        <5>6. UV' = (UV \ {I}) \cup {I1(p), I2(p)}
          BY <5>1, <5>2, <5>3, <5>4, <5>5 DEF UV
        <5>7. TypeOK'
          <6>1. (seq \in Seq(Values) \ {<<>>})'
          <6>2. (seq0 \in Seq(Values) \ {<<>>})'
          <6>3. (U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}}))'
            BY <5>2, <5>3
          <6>4. (pc \in {"a", "Done"})'
            BY <4>1
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4 DEF TypeOK
        <5>8. ((pc = "Done") => (U = {}))'
          BY <4>1
        <5>9. (UV \in DomainPartitions)'
          <6>1. UV' \in SUBSET SUBSET (1..Len(seq0))
            BY <5>6, <5>3, <5>4 <5>1
          <6>2. UNION UV' = 1..Len(seq0)
            BY <5>6, <5>3, <5>4 <5>1
          <6>3. ASSUME NEW J \in UV' PROVE J = Min(J)..Max(J)
            <7>1. CASE J \in UV
              BY <7>1 DEF Inv, DomainPartitions
            <7>2. CASE J = I1(p)
              BY <7>2, <5>3
            <7>3. CASE J = I2(p)
              BY <7>3, <5>3
            <7>4. QED
              BY <7>1, <7>2, <7>3, <5>6
          <6>4. ASSUME NEW J \in UV', NEW K \in UV', J # K PROVE J \cap K = {}
            (***********************************************************)
            (* Follows from the invariant giving the same for UV, and  *)
            (* the definitions of I1(p) and I2(p).                     *)
            (***********************************************************)
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4 DEF DomainPartitions
        <5>10. (seq \in PermsOf(seq0))'
          BY <5>2
        <5>11. (UNION UV = 1..Len(seq0))'
          BY <5>6, <5>3, <5>4, <5>1 DEF Inv
        <5>12. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
          <6>1. ASSUME NEW I_1 \in UV, NEW J \in UV, I_1 # J, NEW i \in I_1, NEW j \in J, i < j
                PROVE seq[i] <= seq[j]
            BY DEF RelSorted
          <6>2. QED
            (***********************************************************)
            (* Follows from the invariant, the definitions of I1(p),  *)
            (* I2(p), and the guard of the case above.                *)
            (***********************************************************)
        <5>13. QED
          BY <5>7, <5>8, <5>9, <5>10, <5>11, <5>12 DEF Inv
      <4>5. QED
        BY <4>3, <4>4
    <3>2. CASE U = {}
      <4>1. TypeOK' /\ ((pc = "Done") => (U = {}))
            /\ (UV \in DomainPartitions) /\ (seq \in PermsOf(seq0))
            /\ (UNION UV = 1..Len(seq0))
            /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))
        OBVIOUS
    <3>3. QED
      BY <3>1, <3>2
  <2>2. CASE UNCHANGED vars
    <3>1. TypeOK' /\ ((pc = "Done") => (U = {}))
          /\ (UV \in DomainPartitions) /\ (seq \in PermsOf(seq0))
          /\ (UNION UV = 1..Len(seq0))
          /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))
      OBVIOUS
    <3>2. QED
      BY <3>1
  <2>3. QED
    BY <2>1, <2>2

<1>3. Inv => PCorrect
  <2>1. /\ seq \in PermsOf(seq0)
        /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]
    BY DEF PCorrect, Inv

<1>4. QED
  BY <1>1, <1>2, <1>3
=============================================================================