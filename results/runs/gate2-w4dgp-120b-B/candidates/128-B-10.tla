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
(* The module sorts a finite sequence of integers.  It is one of the       *)
(* examples in Section 7.3 of "Proving Safety Properties", which is at    *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
  (*************************************************************************)
  (* This statement imports some standard modules, including ones used by  *)
  (* the TLAPS proof system.                                               *)
  (*************************************************************************)

(***************************************************************************)
(* Values is a set of integers; each integer in the sequence to be sorted  *)
(* must belong to it.                                                      *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* PermsOf(s) is the set of all permutations of a sequence s of integers:   *)
(* s composed with any permutation of its domain.  A permutation of a set  *)
(* is a bijection from the set to itself.                                   *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

(***************************************************************************)
(* Max(S) and Min(S) are the maximum and minimum, respectively, of a        *)
(* non-empty set S of integers.                                            *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(***************************************************************************)
(* Partitions(I,p,s) is the set of all arrays that a partition procedure     *)
(* may produce for subinterval I using pivot p: it permutes the entries of   *)
(* s inside I so that everything at or before p is <= everything after p.   *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

\* The algorithm's variables: seq (the array), seq0 (its initial value),   *
\* and U (the set of subintervals still to sort).                         *
VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
  /\ pc \in {"a", "Done"}

DomainPartitions ==
  {DP \in SUBSET SUBSET (1..Len(seq0)) :
     /\ (UNION DP) = 1..Len(seq0)
     /\ \A I \in DP : I = Min(I)..Max(I)
     /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

(***************************************************************************)
(* UV is the partition of the whole index set into the subintervals in U   *)
(* plus a singleton for every index not in any interval of U.               *)
(***************************************************************************)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"
  /\ seq0' = seq0
  /\ UNCHANGED << U, pc >>

\* Choose any interval in U and either discard it if it is a singleton or
\* partition it around a pivot and add the two resulting intervals.
a ==
  /\ pc = "a"
  /\ pc' = IF U = {} THEN "Done" ELSE "a"
  /\ \E I \in U :
       /\ IF Cardinality(I) = 1
            THEN /\ U' = U \ {I}
                 /\ seq' = seq
            ELSE /\ \E p \in Min(I) .. (Max(I)-1) :
                  LET I1 == Min(I)..p IN
                    LET I2 == (p+1)..Max(I) IN
                      \E newseq \in Partitions(I, p, seq) :
                        /\ seq' = newseq
                        /\ U' = ((U \ {I}) \cup {I1, I2})
  /\ UNCHANGED seq0

\* Stutter forever after termination to keep TLC from flagging a deadlock.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(***************************************************************************)
(* The postcondition: if the algorithm terminates, seq is a sorted         *)
(* permutation of seq0.                                                    *)
(***************************************************************************)
PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2>1. OBVIOUS
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. CASE a
    <3>1. \E I \in U :
      <4>1. /\ pc = "a"
            /\ pc' = IF U = {} THEN "Done" ELSE "a"
            /\ I \in U
            /\ Cardinality(I) = 1
            /\ U' = U \ {I}
            /\ seq' = seq
            /\ seq0' = seq0
      <4>2. QED
      <4>1. UV' = UV
        OBVIOUS
      <4>2. TypeOK' /\ ((pc = "Done") => (U = {}))
        OBVIOUS
      <4>3. UV \in DomainPartitions
        OBVIOUS
      <4>4. (seq \in PermsOf(seq0))'
        OBVIOUS
      <4>5. (UNION UV = 1..Len(seq0))'
        OBVIOUS
      <4>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))'
        OBVIOUS
      <4>7. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF Inv
    <3>2. \E I \in U :
      <4>1. /\ pc = "a"
            /\ pc' = IF U = {} THEN "Done" ELSE "a"
            /\ I \in U
            /\ Cardinality(I) # 1
            /\ seq0' = seq0
            /\ \E p \in Min(I) .. (Max(I)-1) :
                 /\ \E newseq \in Partitions(I, p, seq) :
                      /\ seq' = newseq
                      /\ U' = ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)})
      <4>2. LET I1 == Min(I)..p IN LET I2 == (p+1)..Max(I) IN
        /\ Len(seq) = Len(seq')
        /\ Len(seq') = Len(seq0)
        /\ UNION U = UNION U'
        /\ UV' = (UV \ {I}) \cup {I1, I2}
        /\ /\ /\ I1 # {}
              /\ I1 = Min(I1)..Max(I1)
              /\ I1 \subseteq 1..Len(seq0)
           /\ /\ I2 # {}
              /\ I2 = Min(I2)..Max(I2)
              /\ I2 \subseteq 1..Len(seq0)
           /\ I1 \cap I2 = {}
           /\ I1 \cup I2 = I
           /\ \A i \in I1, j \in I2 : (i < j) /\ (seq[i] =< seq[j])
        /\ (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))
          => (\A I_1, J \in UV' : (I_1 # J) => RelSorted(I_1, J))
      <4>3. QED
        BY <4>2
    <3>3. UNCHANGED vars
      OBVIOUS
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>2. CASE UNCHANGED vars
    <3>1. OBVIOUS
  <2>3. QED
    BY <2>1, <2>2 DEF Next
<1>3. Inv => PCorrect
  <2>1. OBVIOUS
<1>4. QED
  BY <1>1, <1>2, <1>3

====