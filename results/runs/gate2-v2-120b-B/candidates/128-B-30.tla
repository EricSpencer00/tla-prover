------------------------------ MODULE Quicksort ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(* Permutations of a sequence *)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] : 
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

Partitions(I, p, s) ==
  { t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j]) }

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

(* Initial state *)
Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

(* The step that mimics the PlusCal loop body *)
a ==
  /\ pc = "a"
  /\ IF U # {}
        THEN /\ \E I \in U :
                IF Cardinality(I) = 1
                   THEN /\ U' = U \ {I}
                        /\ seq' = seq
                   ELSE /\ \E p \in Min(I) .. (Max(I)-1):
                            LET I1 == Min(I)..p IN
                            LET I2 == (p+1)..Max(I) IN
                            \E newseq \in Partitions(I, p, seq):
                               /\ seq' = newseq
                               /\ U' = (U \ {I}) \cup {I1, I2}
        /\ pc' = "a"
        /\ seq0' = seq0
     ELSE /\ pc' = "Done"
          /\ UNCHANGED << seq, U, seq0 >>

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  a \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Termination == <> (pc = "Done")

(* Invariant that captures the intended state of the algorithm *)
Inv ==
  /\ seq \in PermsOf(seq0)
  /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

(* Safety property: when the algorithm terminates, the sequence is sorted
   and is a permutation of the initial sequence. *)
PCorrect ==
  (pc = "Done") => 
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

=============================================================================