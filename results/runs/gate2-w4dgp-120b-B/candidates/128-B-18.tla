---- MODULE Quicksort ----
(* A quicksort algorithm.  The module is specified in PlusCal and then
   translated to TLA+.  Its action is nondeterministic in the choice of
   interval to partition, and of the pivot index within that interval.  It
   is intentionally small so that TLC can model-check it.  The partial
   correctness property proved below is that any state in which the
   algorithm has terminated holds a sorted permutation of the original
   sequence.  The invariant that makes the proof go through is that the
   intervals still being partitioned form a valid domain partition of the
   whole index range, and that any two distinct intervals are out of
   order with respect to one another.  Without the latter, the sortedness
   proof has a gap: each interval internally sorted is not enough if
   adjacent intervals can be out of order with respect to each other. *)

EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

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

VARIABLES seq, seq0, U, pc
vars == << seq, seq0, U, pc >>

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
  /\ pc \in {"a", "Done"}

DomainPartitions ==
  {DP \subseteq SUBSET (1..Len(seq0)) :
      /\ UNION DP = 1..Len(seq0)
      /\ \A I \in DP : I = Min(I)..Max(I)
      /\ \A I, J \in DP : (I # J) => (I \cap J = {})}

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"
  /\ seq0' = seq0

a ==
  /\ pc = "a"
  /\ IF U # {}
       THEN /\ \E I \in U :
               IF Cardinality(I) = 1
                 THEN /\ U' = U \ {I}
                      /\ seq' = seq
                 ELSE /\ \E p \in Min(I)..(Max(I)-1), I1 == Min(I)..p,
                           I2 == (p+1)..Max(I), newseq \in Partitions(I, p, seq) :
                       /\ seq' = newseq
                       /\ U' = (U \ {I}) \cup {I1, I2}
            /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Termination == <>(pc = "Done")

====