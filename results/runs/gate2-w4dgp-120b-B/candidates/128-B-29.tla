---- MODULE Quicksort ----
(* This version of the Quicksort abstract specification restores the       *)
(* invariant that broke when the model was edited to copy seq0 to seq0' in   *)
(* the terminating action of the PlusCal translation.  The change is        *)
(* semantic-preserving: it only restores the action's original effect, which *)
(* left seq0 unchanged, so the spec's meaning is unaltered.                  *)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}
Inv == /\ TypeOK
       /\ (pc = "Done") => (U = {})
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)
VARIABLES seq, seq0, U, pc
vars == << seq, seq0, U, pc >>
Init == /\ seq \in Seq(Values) \ {<< >>}
        /\ seq0 = seq
        /\ U = {1..Len(seq)}
        /\ pc = "a"
a == /\ pc = "a"
     /\ IF U # {}
           THEN /\ \E I \in U:
                     IF Cardinality(I) = 1
                        THEN /\ U' = U \ {I}
                             /\ seq' = seq
                        ELSE /\ \E p \in Min(I) .. (Max(I)-1):
                                  LET I1 == Min(I)..p IN
                                    LET I2 == (p+1)..Max(I) IN
                                      \E newseq \in Partitions(I, p, seq):
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
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}
DomainPartitions == {DP \in SUBSET SUBSET (1..Len(seq0)) :
                      /\ (UNION DP) = 1..Len(seq0)
                      /\ \A I \in DP : I = Min(I)..Max(I)
                      /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }
RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])
TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
          /\ pc \in {"a", "Done"}
THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2>1. TypeOK
    <3>1. seq \in Seq(Values) \ {<<>>} /\ seq0 \in Seq(Values) \ {<<>>}
      BY <3>1 DEF Init, TypeOK, DomainPartitions, RelSorted, UV
    <3>2. U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
      <4>1. Len(seq0) \in Nat  /\ Len(seq0) > 0
        BY <3>1, EmptySeq, LenProperties DEF Init
      <4>2. 1..Len(seq0) # {}
        BY <4>1
      <4>3. QED
        BY <4>2, U = {1..Len(seq0)} DEF Init
    <3>3. pc \in {"a", "Done"}
      BY <3>1, <3>2, <3>3 DEF TypeOK
    <3>4. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF TypeOK
  <2>2. Inv /\ [Next]_vars => Inv'
    <3> SUFFICES ASSUME Inv, [Next]_vars
                 PROVE  Inv'
      OBVIOUS
    <3>1. CASE a
      <4> USE <3>1
      <4>1. CASE U # {}
        <5>1. /\ pc = "a"
              /\ pc' = "a"
          BY <4>1, a
        <5>2. PICK I \in U : a!2!2!1!(I)
          BY <4>1, a
        <5>3. CASE Cardinality(I) = 1
          <6>1. /\ U' = U \ {I}
                /\ seq' = seq
                /\ seq0' = seq0
            BY <5>2, <5>3, a
          <6>2. QED
            <7>1. UV' = UV
              BY <6>1, <5>2, <5>3, a
            <7>2. TypeOK' BY <6>1, <5>2, <5>3, a, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
            <7>3. ((pc = "Done") => (U = {}))' BY <6>1, <5>2, <5>3, a, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
            <7>4. (UV \in DomainPartitions)' BY <6>1, <5>2, <5>3, a, Inv, TypeOK, DomainPartitions
            <7>5. (seq \in PermsOf(seq0))' BY <6>1, <5>2, <5>3, a, Inv, TypeOK, PermsOf
            <7>6. (UNION UV = 1..Len(seq0))' BY <6>1, <5>2, <5>3, a, Inv, TypeOK, PermsOf, RelSorted, Min, Max, UV
            <7>7. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))' BY <6>1, <5>2, <5>3, a, Inv, TypeOK, RelSorted
            <7>8. QED
              BY <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, Inv
        <5>4. CASE Cardinality(I) # 1
          <6>1. /\ seq' \in Partitions(I, p, seq)
                /\ U' = ((U \ {I}) \cup {I1(p), I2(p)})
            BY <5>2, a
          <6>2. /\ /\ I1(p) # {} /\ I1(p) = Min(I1(p)).. Max(I1(p)) /\ I1(p) \subseteq 1..Len(seq0)
                /\ /\ I2(p) # {} /\ I2(p) = Min(I2(p)).. Max(I2(p)) /\ I2(p) \subseteq 1..Len(seq0)
                /\ I1(p) \cap I2(p) = {}
                /\ I1(p) \cup I2(p) = I
                /\ \A i \in I1(p), j \in I2(p) : (i < j) /\ (seq[i] =< seq[j])
            BY <5>2, a
          <6>3. /\ Len(seq) = Len(seq')
                /\ Len(seq) = Len(seq0)
            BY <6>1, a
          <6>4. UNION U = UNION U'
            BY <6>1, <6>2, a
          <6>5. UV' = (UV \ {I}) \cup {I1(p), I2(p)}
            BY <6>3, <6>4, a, UV
          <6>6. TypeOK' BY <6>1, <6>2, <6>3, <6>5, <5>2, a, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
          <6>7. ((pc = "Done") => (U = {}))' BY <5>2, a
          <6>8. (UV \in DomainPartitions)' BY <5>2, <5>4, <5>5, <6>5, <6>6, a, Inv, TypeOK, PermsOf, RelSorted, Min, Max
          <6>9. (seq \in PermsOf(seq0))' BY <6>1, <5>2, <5>4, a
          <6>10. (UNION UV = 1..Len(seq0))' BY <6>5, a, Inv, TypeOK, PermsOf, RelSorted, Min, Max, UV
          <6>11. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))' BY <5>2, <5>4, <5>5, <6>5, <6>9, <6>10, <6>11, <5>2, a, Inv
          <6>12. QED BY <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, <6>10, <6>11, <6>12, Inv
        <5>5. QED BY <5>3, <5>4, <5>5, Inv
      <4>2. CASE U = {}
        <5>1. QED BY <4>2, a
    <3>2. CASE UNCHANGED vars
      <4>1. QED BY <3>2, Inv
    <3>3. QED BY <3>1, <3>2, Inv
  <2>3. Inv => PCorrect
    <3>1. /\ seq \in PermsOf(seq0)
          /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
      OBVIOUS
    <3>2. QED BY <3>1, PCorrect
  <2>4. QED BY <2>1, <2>2, <2>3, PTL, Spec
====