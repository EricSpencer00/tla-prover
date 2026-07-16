---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

(*-----------------------------------------------------------------------*)
(* Constants                                                             *)
(*-----------------------------------------------------------------------*)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(*-----------------------------------------------------------------------*)
(* Helper definitions                                                    *)
(*-----------------------------------------------------------------------*)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Partitions(I, p, s) ==
  { t \in PermsOf(s) :
        /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
        /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j]) }

(*-----------------------------------------------------------------------*)
(* Variables                                                             *)
(*-----------------------------------------------------------------------*)
VARIABLES seq, seq0, U, pc, UV

vars == << seq, seq0, U, pc, UV >>

(*-----------------------------------------------------------------------*)
(* Initial state                                                         *)
(*-----------------------------------------------------------------------*)
Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ UV = {1..Len(seq)}
  /\ pc = "a"

(*-----------------------------------------------------------------------*)
(* Actions                                                               *)
(*-----------------------------------------------------------------------*)
a ==
  /\ pc = "a"
  /\ IF U # {}
        THEN
          /\ \E I \in U :
                IF Cardinality(I) = 1
                   THEN /\ U' = U \ {I}
                        /\ seq' = seq
                        /\ UV' = UV
                   ELSE
                        /\ \E p \in Min(I) .. (Max(I)-1) :
                              LET I1 == Min(I)..p IN
                              LET I2 == (p+1)..Max(I) IN
                              \E newseq \in Partitions(I, p, seq) :
                                   /\ seq' = newseq
                                   /\ U' = (U \ {I}) \cup {I1, I2}
                                   /\ UV' = (UV \ {I}) \cup {I1, I2}
          /\ pc' = "a"
        ELSE
          /\ pc' = "Done"
          /\ UNCHANGED << seq, U, UV >>
  /\ UNCHANGED seq0

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED << seq, seq0, U, UV >>

Next == a \/ Terminating

(*-----------------------------------------------------------------------*)
(* Specification                                                         *)
(*-----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------------*)
(* Type correctness invariant (kept for readability)                    *)
(*-----------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
  /\ UV \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
  /\ pc \in {"a", "Done"}

(*-----------------------------------------------------------------------*)
(* Invariant Inv (the one that was violated)                             *)
(*-----------------------------------------------------------------------*)
Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

DomainPartitions ==
  { DP \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} ) :
        /\ (UNION DP) = 1..Len(seq0)
        /\ \A I \in DP : I = Min(I)..Max(I)
        /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) ==
  \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

(*-----------------------------------------------------------------------*)
(* Postcondition PCorrect                                                *)
(*-----------------------------------------------------------------------*)
PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

=============================================================================