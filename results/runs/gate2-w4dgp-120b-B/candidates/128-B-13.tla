---- MODULE Quicksort ----
(* Quicksort -- abstracted: partition chooses any allowed pivot split at once. *)
(* Partial correctness proved (termination is separate) by TLAPS.                *)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME Values \subseteq Int

(* Permutations of a sequence: compositions of it with permutations of its domain. *)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(* New values a partition may produce: unchanged outside I, values left of p *)
(* not greater than values right of p.                                          *)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
     /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
     /\ \A i \in I, j \in I : (i <= p /\ p < j) => (t[i] <= t[j])}

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions == {DP \subseteq SUBSET (1..Len(seq0)) :
  /\ (UNION DP) = 1..Len(seq0)
  /\ \A I \in DP : I = Min(I)..Max(I)
  /\ \A I, J \in DP : (I # J) => (I \cap J = {})}

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \in SUBSET (SUBSET (1..Len(seq0)) \ {{}})
          /\ pc \in {"a", "Done"}

Inv == /\ TypeOK
       /\ (pc = "Done") => (U = {})
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

VARIABLES seq, seq0, U, pc
vars == << seq, seq0, U, pc >>

Init == /\ seq \in Seq(Values) \ {<<>>}
        /\ seq0 = seq
        /\ U = {1..Len(seq)}
        /\ pc = "a"

(* The Quicksort step: choose an interval in U and partition it unless it is *)
(* a singleton, in which case it is removed from further consideration.      *)
a == /\ pc = "a"
     /\ IF U # {}
          THEN /\ \E I \in U :
                  IF Cardinality(I) = 1
                    THEN /\ U' = U \ {I}
                         /\ seq' = seq
                    ELSE /\ \E p \in Min(I)..(Max(I)-1),
                            I1 == Min(I)..p,
                            I2 == (p+1)..Max(I),
                            newseq \in Partitions(I, p, seq):
                         /\ seq' = newseq
                         /\ U' = ((U \ {I}) \cup {I1, I2})
               /\ pc' = "a"
          ELSE /\ pc' = "Done" /\ UNCHANGED << seq, U >>
     /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(* Postcondition: on termination the array is a sorted permutation of the   *)
(* original.  In particular this is *not* a vacuity-trap (U empty but seq  *)
(* unchanged) unless the original was already sorted.                     *)
PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2>1. By inspection of the initial state:
       /\ seq \in Seq(Values) \ {<<>>}
       /\ seq0 \in Seq(Values) \ {<<>>}
       /\ U = {1..Len(seq)}
       /\ pc = "a"
       /\ UV = {1..Len(seq)} \in DomainPartitions
       /\ UNION UV = 1..Len(seq)
       /\ \A I \in UV : I = Min(I)..Max(I)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)
       /\ seq \in PermsOf(seq0)
  <2>2. QED

<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. By a case on the step chosen:
    <3>CASE a
      <4>1. pc = "a" /\ U # {}: let I \in U be the chosen interval.
        <5>CASE Cardinality(I) = 1
          <6>1. U' = U \ {I}, seq' = seq
          <6>2. UV' = UV, TypeOK' (U, seq unchanged)
          <6>3. UV' \in DomainPartitions by I \in UV and the unchanged nature of U.
          <6>4. QED
        <5>2. Cardinality(I) > 1: let p \in Min(I)..(Max(I)-1),
              I1 == Min(I)..p, I2 == (p+1)..Max(I), seq' \in Partitions(I, p, seq).
          <6>1. U' = (U \ {I}) \cup {I1, I2}
          <6>2. UV' = (UV \ {I}) \cup {I1, I2}
          <6>3. TypeOK' (Lengths unchanged, U a subset of subintervals)
          <6>4. UV' \in DomainPartitions: each I1, I2 is a non-empty subinterval,
                they partition I, and RelSorted holds across all of UV' by the
                definition of Partitions(I, p, seq).
          <6>5. QED
      <4>2. pc = "a" /\ U = {}: this is the self-loop in the terminating case;
           all four components are unchanged, so Inv is preserved.
    <3>CASE UNCHANGED vars: same as the terminating self-loop.
  <2>2. QED

<1>3. Inv => PCorrect
  <2>1. By the definition of UV in Inv, each index i is its own singleton in UV,
       so RelSorted({i}, {j}) yields seq[i] <= seq[j] for all i < j.
  <2>2. QED

====