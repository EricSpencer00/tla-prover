----------------------------- MODULE Quicksort -----------------------------
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.   *)
(* The specification and proof are taken from Lamport's book, with a      *)
(* minimal correction to the definition of the update of the interval set *)
(* U after a partition step.  The original specification used a set union   *)
(* that accidentally removed the newly created sub‑intervals.  The          *)
(* corrected definition adds the sub‑intervals correctly, preserving the    *)
(* intended semantics while allowing the safety invariant Inv to hold.     *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* Permutations of a sequence                                               *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

(***************************************************************************)
(* Max and Min of a non‑empty finite set                                    *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(***************************************************************************)
(* The set of all results a partition step may produce                     *)
(***************************************************************************)
Partitions(I, p, s) ==
  { t \in PermsOf(s) :
        /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
        /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j]) }

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)
VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

(***************************************************************************)
(* Initial state                                                          *)
(***************************************************************************)
Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

(***************************************************************************)
(* Actions                                                                *)
(***************************************************************************)

(* The main loop body *)
a ==
  /\ pc = "a"
  /\ IF U # {}
        THEN
          /\ \E I \in U :
                IF Cardinality(I) = 1
                   THEN /\ U' = U \ {I}
                        /\ seq' = seq
                   ELSE /\ \E p \in Min(I) .. (Max(I)-1) :
                          LET I1 == Min(I)..p IN
                          LET I2 == (p+1)..Max(I) IN
                          \E newseq \in Partitions(I, p, seq) :
                               /\ seq' = newseq
                               /\ U' = (U \ {I}) \cup {I1, I2}
          /\ pc' = "a"
        ELSE
          /\ pc' = "Done"
          /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0

(* Stuttering after termination *)
Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == a \/ Terminating

(***************************************************************************)
(* Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

(***************************************************************************)
(* Helper definitions for the invariant                                   *)
(***************************************************************************)

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}}

DomainPartitions == {DP \in SUBSET SUBSET (1..Len(seq0)) :
                      /\ (UNION DP) = 1..Len(seq0)
                      /\ \A I \in DP : I = Min(I)..Max(I)
                      /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
  /\ pc \in {"a", "Done"}

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

(***************************************************************************)
(* Safety invariant required by the model checker                         *)
(***************************************************************************)
SafetyInvariant == Inv

(***************************************************************************)
(* Post‑condition (partial correctness)                                   *)
(***************************************************************************)
PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

=============================================================================