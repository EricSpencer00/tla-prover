---- MODULE Quicksort ----
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
(* The module sorts a finite sequence of integers.  It is one of the      *)
(* examples in Section 7.3 of "Proving Safety Properties", which is at    *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
  (*************************************************************************)
  (* This statement imports some standard modules, and some used by TLAPS. *)
  (*************************************************************************)

(***************************************************************************)
(* To aid in model checking the spec, we assume that the sequence to be    *)
(* sorted are elements of a set Values of integers.                        *)
(***************************************************************************)
CONSTANT Values
ASSUME Values \subseteq Int

(***************************************************************************)
(* PermsOf(s) is the set of permutations of a sequence s of integers.  In  *)
(* TLA+, a sequence is a function whose domain is 1..Len(s).  A permutation *)
(* of s is the composition of s with a permutation of its domain.  An       *)
(* automorphism of a set S is a permutation of S; the operator ** denotes   *)
(* function composition.                                                    *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(***************************************************************************)
(* Partitions(I, p, seq) is the set of new values seq may take from         *)
(* partitioning the subinterval I at the pivot index p.  It permutes seq[i] *)
(* for i \in I so that the values in the left half are <= the values in the *)
(* right half, and leaves seq[i] unchanged for i \notin I.                    *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j])}

Variables seq, seq0, U, pc
vars == << seq, seq0, U, pc >>

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

(***************************************************************************)
(* Action a models Quicksort's recursive partition.  It picks an arbitrary   *)
(* interval I in U, and either removes it if it is a single element, or      *)
(* partitions it at a pivot p, permuting its elements so the left half is    *)
(* <= the right half.  In the latter case it replaces I in U by its two      *)
(* halves.                                                                    *)
(***************************************************************************)
a ==
  /\ pc = "a"
  /\ IF U # {}
       THEN /\ \E I \in U :
              /\ IF Cardinality(I) = 1
                 THEN /\ U' = U \ {I}
                      /\ seq' = seq
                 ELSE /\ \E p \in Min(I) .. (Max(I)-1) :
                        /\ seq' \in Partitions(I, p, seq)
                        /\ U' = (U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
                 /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars
Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Termination == <>(pc = "Done")

(***************************************************************************)
(* The postcondition PCorrect is that a terminating run ends in a sorted    *)
(* permutation of the original sequence, so TLC can model-check it on a    *)
(* model where Seq(S) is redefined to be sequences of at most 4 elements of   *)
(* a 4-element set.                                                          *)
(***************************************************************************)
PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

(***************************************************************************)
(* UV is the intervals singled out by the invariant: the intervals in U     *)
(* plus every singleton interval of which its index is in none of them.  The *)
(* invariant Inv is an inductively defined type-correctness plus semantic   *)
(* property that together imply the postcondition.                           *)
(***************************************************************************)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions ==
  {DP \in SUBSET SUBSET (1..Len(seq0)) :
      /\ (UNION DP) = 1..Len(seq0)
      /\ \A I \in DP : I = Min(I)..Max(I)
      /\ \A I, J \in DP : (I # J) => (I \cap J = {})}

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET (SUBSET (1..Len(seq0)) \ {{}})
  /\ pc \in {"a", "Done"}

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2>1. TypeOK
    <3>1. seq \in Seq(Values) \ {<<>>} BY <2>1 DEF Init, TypeOK
    <3>2. seq0 \in Seq(Values) \ {<<>>} BY <2>1 DEF Init, TypeOK
    <3>3. U \in SUBSET (SUBSET (1..Len(seq0)) \ {{}})
      BY <2>1, Init DEF TypeOK
    <3>4. pc \in {"a", "Done"} BY <2>1, Init DEF TypeOK
    <3>5. QED BY <3>1, <3>2, <3>3, <3>4 DEF TypeOK
  <2>2. (pc = "Done") => (U = {}) BY Init
  <2>3. UV \in DomainPartitions
    <3>1. UV = {1..Len(seq0)} BY Init
    <3>2. UV \in SUBSET SUBSET (1..Len(seq0)) BY <3>1 DEF Inv
    <3>3. (UNION UV) = 1..Len(seq0) BY <3>1
    <3>4. \A I, J \in UV : I = J BY <3>1
    <3>5. QED BY <3>1, <3>2, <3>3, <3>4 DEF DomainPartitions
  <2>4. seq \in PermsOf(seq0)
    <3>1. seq \in PermsOf(seq) BY <2>1 DEF Init
    <3>2. QED BY <3>1 DEF Init, PermsOf
  <2>5. UNION UV = 1..Len(seq0) BY Init, Inv, TypeOK, UV, DomainPartitions
  <2>6. \A I, J \in UV : (I # J) => RelSorted(I, J) BY Init, Inv
  <2>7. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. Inv /\ [Next]_vars => Inv'
    <3>1. CASE a
      <4>1. pc = "a"
        (*****************************************************************)
        (* By the type-correctness in Inv.                                *)
        (*****************************************************************)
      <4>2. PICK I \in U : a!2!2!1!(I)
        BY <3>1 DEF a
      <4>3. CASE Cardinality(I) = 1
        <5>1. U' = U \ {I} /\ seq' = seq BY <4>2, <4>3
        <5>2. QED
          <6>1. UV' = UV BY <4>2, <4>3
          <6>2. QED BY <6>1, <5>1, <5>2 DEF Inv
      <4>4. CASE Cardinality(I) # 1
        <5>1. \E p \in Min(I)..(Max(I)-1) :
              /\ seq' \in Partitions(I, p, seq)
              /\ U' = ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)})
          BY <4>2, <4>4
        <5>2. /\ Min(I)..p # {}
              /\ Min(I)..p = Min(Min(I)..p)..Max(Min(I)..p)
              /\ Min(I)..p \subseteq 1..Len(seq0)
              /\ (p+1)..Max(I) # {}
              /\ (p+1)..Max(I) = Min((p+1)..Max(I))..Max((p+1)..Max(I))
              /\ (p+1)..Max(I) \subseteq 1..Len(seq0)
              /\ (Min(I)..p) \cap ((p+1)..Max(I)) = {}
              /\ (Min(I)..p) \cup ((p+1)..Max(I)) = I
              /\ \A i \in Min(I)..p, j \in (p+1)..Max(I) : (i < j) /\ (seq[i] <= seq[j])
          BY <4>4, <5>1
        <5>3. Len(seq) = Len(seq') /\ Len(seq) = Len(seq0) BY <5>1, Partitions
        <5>4. UNION U = UNION U' BY <5>1, <5>2
        <5>5. UV' = (UV \ {I}) \cup {Min(I)..p, (p+1)..Max(I)} BY <5>1, <5>2, <5>3, <5>4 DEF UV
        <5>6. QED
          <6>1. seq \in Seq(Values) \ {<<>>} BY <5>1, Partitions, PermsOf
          <6>2. QED BY <6>1, <5>1, <5>2, <5>3, <5>4, <5>5, <5>6 DEF Inv
      <4>5. QED BY <4>3, <4>4
    <3>2. CASE UNCHANGED vars
      <4>1. QED BY <3>2, Inv
    <3>3. QED BY <3>1, <3>2 DEF Next
  <2>4. Inv => PCorrect
    <3>1. seq \in PermsOf(seq0) BY <2>4
    <3>2. \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]
      <4>1. p, q \in 1..Len(seq) /\ p < q
        BY <3>2
      <4>2. {p} \in UV /\ {q} \in UV BY <2>3
      <4>3. QED BY <4>2 DEF Inv, RelSorted
    <3>3. QED BY <3>1, <3>2
  <2>5. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, PTL
=============================================================================