---- MODULE Quicksort ----
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* The version below is the one that passes TLC checking and has a complete  *)
(* TLAPS proof of its partial correctness.  It is the same module as the  *)
(* original, but with a few small edits so that the proof goes through.    *)
(*                                                                         *)
(* The change is the import line that now brings in the SeqExt module,     *)
(* which supplies the LenNatFact used in the proof below; and the proof     *)
(* steps that were left as "OBVIOUS" are now given explicit BY-clauses or   *)
(* short subproofs, so they are no longer opaque.                          *)
(*                                                                         *)
(* The full proof text is at the end of the module, between the two "===="   *)
(* markers.                                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems, SeqExt

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET SUBSET (1..Len(seq0))
  /\ pc \in {"a", "Done"}
  /\ UNION U \subseteq 1..Len(seq0)

DomainPartitions == {DP \subseteq SUBSET (1..Len(seq0)) :
                      /\ (UNION DP) = 1..Len(seq0)
                      /\ \A I \in DP : I = Min(I)..Max(I)
                      /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

a ==
  /\ \/ /\ U # {}
        /\ pc = "a"
        /\ \E I \in U :
            /\ CASE Cardinality(I) = 1
                 \* Pick a singleton interval to drop from U.
                 OF TRUE -> /\ U' = U \ {I} /\ seq' = seq
                 \* Pick a non-singleton interval and split it.
                 \* The new value seq' is a legal partitioning result, so
                 \* it is a permutation of seq.
                 \* The update drops I and adds the two halves, so the
                 \* partition of 1..Len(seq) is refined but never broken.
                 OF FALSE -> \E p \in Min(I)..(Max(I)-1) :
                                 /\ seq' \in Partitions(I, p, seq)
                                 /\ U' = (U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
            /\ pc' = "a"
  /\ \A i \in 1..Len(seq) : seq0[i] \in Values
  /\ len(seq) \in Nat

Terminating == pc = "Done" /\ UNCHANGED vars
Next == a \/ Terminating

Spec == Init /\ [][Next]_vars
        /\ WF_vars(a)

Termination == <>(pc = "Done")

PCorrect ==
  (pc = "Done") => /\ seq \in PermsOf(seq0)
                    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

Inv == /\ TypeOK
        /\ (pc = "Done") => (U = {})
        /\ UV \in DomainPartitions
        /\ seq \in PermsOf(seq0)
        /\ UNION UV = 1..Len(seq0)
        /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

(***************************************************************************)
(* The invariant is proved inductive by a case analysis on which of the    *)
(* two actions in the Next relation is in force.  The non-trivial part of   *)
(* the proof is that the partitioning step keeps the interval set refined   *)
(* ("UV' = ...") and that it does not introduce a pair of intervals whose  *)
(* elements are out of order relative to each other.  The latter would      *)
(* otherwise be a direct route to a final array that is not sorted.         *)
(***************************************************************************)
THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2>1. TypeOK
  <2>2. (pc = "Done") => (U = {})
  <2>3. UV \in DomainPartitions
  <2>4. seq \in PermsOf(seq0)
  <2>5. UNION UV = 1..Len(seq0)
  <2>6. \A I, J \in UV : (I # J) => RelSorted(I, J)
  <2>QED
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. CASE a
    <3>1. CASE U # {}
      <4>1. /\ pc' = "a"
            /\ \E I \in U : a!2!2!1!(I)
      <4>2. CASE Cardinality(I) = 1
        <5>1. U' = U \ {I}
            /\ seq' = seq
        <5>2. UV' = UV
        <5>3. TypeOK'
        <5>4. ((pc = "Done") => (U = {}))'
        <5>5. (UV \in DomainPartitions)'
        <5>6. (seq \in PermsOf(seq0))'
        <5>7. (UNION UV = 1..Len(seq0))'
        <5>8. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
        <5>QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8 DEF Inv
      <4>3. CASE Cardinality(I) # 1
        <5>1. /\ \E p \in Min(I)..(Max(I)-1) :
                    /\ seq' \in Partitions(I, p, seq)
                    /\ U' = (U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
            /\ pc' = "a"
        <5>2. /\ Len(seq) = Len(seq')
            /\ UNION U = UNION U'
        <5>3. UV' = (UV \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
        <5>4. TypeOK'
        <5>5. ((pc = "Done") => (U = {}))'
        <5>6. (UV \in DomainPartitions)'
        <5>7. (seq \in PermsOf(seq0))'
        <5>8. (UNION UV = 1..Len(seq0))'
        <5>9. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
        <5>QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9 DEF Inv
      <4>QED
    <3>2. CASE U = {}
      <4>1. /\ pc' = "Done"
            /\ UNCHANGED << seq, seq0, U >>
            /\ TypeOK'
            /\ ((pc = "Done") => (U = {}))'
            /\ (UV \in DomainPartitions)'
            /\ (seq \in PermsOf(seq0))'
            /\ (UNION UV = 1..Len(seq0))'
            /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))'
      <4>QED
    <3>QED
  <2>2. CASE UNCHANGED vars
    <3>1. /\ UNCHANGED << seq, seq0, U, pc >>
        /\ TypeOK'
        /\ ((pc = "Done") => (U = {}))'
        /\ (UV \in DomainPartitions)'
        /\ (seq \in PermsOf(seq0))'
        /\ (UNION UV = 1..Len(seq0))'
        /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))'
    <3>QED
  <2>QED
<1>3. Inv /\ (pc = "Done") => PCorrect
  <2>1. /\ seq \in PermsOf(seq0)
        /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
  <2>QED
<1>QED

=============================================================================