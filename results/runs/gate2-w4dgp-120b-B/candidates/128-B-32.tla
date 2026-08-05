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
(* The module sorts a finite sequence of integers.  It is one of the       *)
(* examples in Section 7.3 of "Proving Safety Properties", which is at     *)
(* http://lamport.azurewebsites.net/tla/proving-safety.pdf.                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* PermsOf(s) is the set of permutations of a sequence s of integers.      *)
(* In TLA+, a sequence is a function whose domain is 1..Len(s).  A         *)
(* permutation of s is the composition of s with a permutation of its        *)
(* domain.  The definition uses f ** g for the composition of f and g.      *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(***************************************************************************)
(* Partitions(I, p, seq) is the set of new values of sequence seq that a    *)
(* partition procedure is allowed to produce for the subinterval I using   *)
(* the pivot index p: it permutes the values of seq[i] for i \in I so that   *)
(* the values for i =< p are less than or equal to the values for i > p.    *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

DOMAINPARTITIONS == {DP \in SUBSET SUBSET (1..Len(seq0)) :
                      /\ (UNION DP) = 1..Len(seq0)
                      /\ \A I \in DP : I = Min(I)..Max(I)
                      /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
  /\ pc \in {"a", "Done"}

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

Inv == /\ TypeOK
       /\ (pc = "Done") => (U = {})
       /\ UV \in DOMAINPARTITIONS
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

Init == /\ seq \in Seq(Values) \ {<<>>}
        /\ seq0 = seq
        /\ U = {1..Len(seq)}
        /\ pc = "a"
        /\ seq0' = seq0

a == /\ pc = "a"
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
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << seq, U >>
     /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

PCorrect == (pc = "Done") => /\ seq \in PermsOf(seq0)
                              /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

THEOREM Spec => []PCorrect
<1>1. (Init => Inv) /\ (Inv /\ [Next]_vars => Inv')
     <2>1. SUFFICES ASSUME Init PROVE Inv
       <3>1. TypeOK
         (*******************************************************************)
         (* This follows directly from the definition of Init.            *)
         (*******************************************************************)
         BY DEF Init, Inv, DOMAINPARTITIONS, RelSorted, UV
       <3>2. (pc = "Done") => (U = {})
         BY DEF Init, Inv
       <3>3. UV \in DOMAINPARTITIONS
         <4>1. UV = {1..Len(seq0)} BY DEF UV, Init
         <4>2. UV \in SUBSET SUBSET (1..Len(seq0))
           BY DEF DOMAINPARTITIONS, <4>1
         <4>3. (UNION UV) = 1..Len(seq0) BY <4>1
         <4>4. \A I, J \in UV : I = J
           BY DEF UV, Init
         <4>5. QED
           BY <4>1, <4>2, <4>3, <4>4, DEF DOMAINPARTITIONS
       <3>4. seq \in PermsOf(seq0)
         (*******************************************************************)
         (* The identity function shows seq \in PermsOf(seq).               *)
         (*******************************************************************)
         BY DEF Init, Inv, PermsOf
       <3>5. (UNION UV) = 1..Len(seq0) BY DEF Init, Inv, UV
       <3>6. \A I, J \in UV : (I # J) => RelSorted(I, J) BY DEF Init, Inv, RelSorted
       <3>7. QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, DEF Inv
     <2>2. SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
       <3> CASE a
         <4>1. LET p == CHOOSE x \in Min(I)..(Max(I)-1) : TRUE
                  I1 == Min(I)..p
                  I2 == (p+1)..Max(I) IN
                <5>1. CASE Cardinality(I) = 1
                  <6>1. /\ pc = "a" /\ pc' = "a"
                        /\ U' = U \ {I} /\ seq' = seq /\ seq0' = seq0
                        /\ UV' = UV
                        /\ TypeOK' /\ ((pc = "Done") => (U = {}))
                        /\ (UV' \in DOMAINPARTITIONS) /\ (seq' \in PermsOf(seq0))
                        /\ (UNION UV' = 1..Len(seq0))
                        /\ (\A I_1, J \in UV' : (I_1 # J) => RelSorted(I_1, J))
                  <6>2. QED
                    (***********************************************************)
                    (* A singleton I is removed from U; since UV also adds {j} *)
                    (* for every j in the complement, UV stays unchanged.      *)
                    (***********************************************************)
                <5>2. CASE Cardinality(I) # 1
                  <6>1. /\ pc = "a" /\ pc' = "a" /\ seq0' = seq0
                        /\ /\ I1 # {} /\ I1 = Min(I1)..Max(I1) /\ I1 \subseteq 1..Len(seq0)
                           /\ /\ I2 # {} /\ I2 = Min(I2)..Max(I2) /\ I2 \subseteq 1..Len(seq0)
                              /\ /\ I1 \cap I2 = {} /\ I1 \cup I2 = I
                                 /\ \A i \in I1, j \in I2 : (i < j) /\ (seq[i] =< seq[j])
                        /\ seq' \in Partitions(I, p, seq)
                        /\ U' = ((U \ {I}) \cup {I1, I2})
                        /\ UV' = (UV \ {I}) \cup {I1, I2}
                        /\ TypeOK' /\ ((pc = "Done") => (U = {}))
                        /\ (UV' \in DOMAINPARTITIONS) /\ (seq' \in PermsOf(seq0))
                        /\ (UNION UV' = 1..Len(seq0))
                        /\ (\A I_1, J \in UV' : (I_1 # J) => RelSorted(I_1, J))
                        /\ Len(seq') = Len(seq) /\ Len(seq) = Len(seq0)
                  <6>2. QED
                    (***********************************************************)
                    (* The interval I is split into I1 and I2, which the action  *)
                    (* adds to U and UV.  The partition property gives the last*)
                    (* conjunct.                                               *)
                    (***********************************************************)
               <5>3. QED
         <4>2. CASE U = {}
           <5>1. /\ pc' = "Done" /\ UNCHANGED << seq, seq0, U >>
                 /\ TypeOK' /\ ((pc = "Done") => (U = {})) /\ (UV \in DOMAINPARTITIONS)
                 /\ (seq \in PermsOf(seq0)) /\ (UNION UV = 1..Len(seq0))
                 /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))
           <5>2. QED
       <3> CASE UNCHANGED vars
         <4>1. TypeOK' /\ ((pc = "Done") => (U = {}))
               /\ (UV \in DOMAINPARTITIONS) /\ (seq \in PermsOf(seq0))
               /\ (UNION UV = 1..Len(seq0))
               /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))
         <4>2. QED
       <3>3. QED BY <3>1, <3>2, DEF Next
     <2>3. (Inv => PCorrect)
       <3> SUFFICES ASSUME Inv, pc = "Done" PROVE
             /\ seq \in PermsOf(seq0)
             /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
         <4>1. seq \in PermsOf(seq0) BY DEF Inv
         <4>2. \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
           <5>1. LET J == {i} : i \in p..q IN
                 LET I == {i} : i \in 1..Len(seq) IN
                 <6>1. /\ Len(seq) = Len(seq0) /\ Len(seq) \in Nat /\ Len(seq) > 0
                         /\ UV = {{i} : i \in 1..Len(seq)}
                       BY DEF Inv, I
                   <6>2. {p} \in UV /\ {q} \in UV
                     (*******************************************************************)
                     (* Both indices lie in singleton intervals of UV, so RelSorted    *)
                     (* applies.                                                        *)
                     (*******************************************************************)
                     BY <6>1, <6>2
               <5>2. QED BY <5>1, DEF Inv, RelSorted
         <4>3. QED BY <4>1, <4>2
       <3>4. QED BY <2>1, <2>2, <2>3, PTL DEF Spec
<1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================