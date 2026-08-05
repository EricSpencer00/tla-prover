---- MODULE Quicksort ------------------------------------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
CONSTANT Values
ASSUME Values \subseteq Int

(*
An abstract Quicksort on a finite sequence of integers.  PermsOf(s) is the
set of permutations of a sequence s.  The algorithm keeps U, the set of
intervals still to be sorted, and only ever permutes the elements of a
chosen interval.  It terminates when no interval remains.
*)

PermsOf(s) ==
  LET Automorphisms(S) ==
        { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Partitions(I, p, s) ==
  {t \in PermsOf(s) :
     /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
     /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j])}

DomainPartitions ==
  { DP \subseteq SUBSET (1..Len(seq0)) :
      /\ (UNION DP) = 1..Len(seq0)
      /\ \A I \in DP : I = Min(I)..Max(I)
      /\ \A I, J \in DP : I # J => I \cap J = {} }

RelSorted(I, J) ==
  \A i \in I, j \in J : i < j => seq[i] <= seq[j]

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>
TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \subseteq (SUBSET (1..Len(seq0))) \ {{}} /\ pc \in {"a", "Done"}

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)} /\ pc = "a"

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

Inv == /\ TypeOK
       /\ (pc = "Done") => U = {}
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : I # J => RelSorted(I, J)

a ==
  /\ pc = "a" /\ IF U # {}
       THEN \E I \in U :
              /\ IF Cardinality(I) = 1
                 THEN /\ U' = U \ {I} /\ seq' = seq
                 ELSE \/ (\E p \in Min(I)..(Max(I)-1), I1 = Min(I)..p,
                                 I2 = (p+1)..Max(I), t \in Partitions(I, p, seq) :
                         /\ seq' = t
                         /\ U' = ((U \ {I}) \cup {I1, I2}))
              /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars
Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a) /\ WF_vars(Terminating)

PCorrect ==
  (pc = "Done") => /\ seq \in PermsOf(seq0)
                    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

termination == <>(pc = "Done")

THEOREM Spec => []PCorrect
<1>1. Init => Inv
     <2>1. /\ Len(seq0) \in Nat /\ Len(seq0) > 0
          BY Init, LenProperties
     <2>2. UV = {1..Len(seq0)}
          BY <2>1, Init
     <2>3. \A I \in UV : I = Min(I)..Max(I)
          BY <2>2
     <2>4. \A I, J \in UV : I # J => RelSorted(I, J)
          BY <2>2
     <2>5. seq \in PermsOf(seq0)
          BY Init, PermsOf
     <2>6. UNION UV = 1..Len(seq0)
          BY <2>2
     <2>7. QED BY <2>2, <2>3, <2>4, <2>5, <2>6, Inv

<1>2. Inv /\ [Next]_vars => Inv
     <2>1. CASE a
       <3>1. CASE U # {}
         <4>1. \E I \in U :
                /\ IF Cardinality(I) = 1
                     THEN /\ U' = U \ {I} /\ seq' = seq
                     ELSE \E p \in Min(I)..(Max(I)-1), I1 = Min(I)..p,
                                 I2 = (p+1)..Max(I), t \in Partitions(I, p, seq) :
                              /\ seq' = t /\ U' = ((U \ {I}) \cup {I1, I2})
                /\ pc' = "a"
               /\ seq0' = seq0
         <4>2. CASE Cardinality(I) = 1
           <5>1. /\ U' = U \ {I} /\ seq' = seq /\ seq0' = seq0
                 /\ pc' = "a"
                 /\ UV' = UV
                 /\ TypeOK' /\ ((pc = "Done") => U' = {})
                 /\ UV' \in DomainPartitions
                 /\ seq' \in PermsOf(seq0')
                 /\ UNION UV' = 1..Len(seq0')
                 /\ \A I_1, J \in UV' : I_1 # J => RelSorted(I_1, J)
                 BY <4>1, <4>2, <4>1
         <4>3. CASE Cardinality(I) # 1
           <5>1. \E p \in Min(I)..(Max(I)-1), I1 = Min(I)..p,
                     I2 = (p+1)..Max(I), t \in Partitions(I, p, seq) :
                    /\ seq' = t /\ U' = ((U \ {I}) \cup {I1, I2})
                 /\ pc' = "a" /\ seq0' = seq0
           <5>2. /\ I1 # {} /\ I1 = Min(I1)..Max(I1)
                 /\ I2 # {} /\ I2 = Min(I2)..Max(I2)
                 /\ I1 \cap I2 = {} /\ I1 \cup I2 = I
                 /\ \A i \in I1, j \in I2 : i < j /\ seq[i] <= seq[j]
                 /\ UV' = (UV \ {I}) \cup {I1, I2}
                 /\ TypeOK' /\ ((pc = "Done") => U' = {})
                 /\ UV' \in DomainPartitions
                 /\ seq' \in PermsOf(seq0')
                 /\ UNION UV' = 1..Len(seq0')
                 /\ \A I_1, J \in UV' : I_1 # J => RelSorted(I_1, J)
                 BY <5>1, <5>2
                 (***********************************************************)
                 (* UV' \in DomainPartitions holds because UV was a          *)
                 (* partition and I is split into the disjoint subintervals *)
                 (* I1 and I2, which are themselves subintervals.           *)
                 (***********************************************************)
       <3>2. CASE U = {}
         <4>1. /\ UV \in DomainPartitions
               /\ seq \in PermsOf(seq0) /\ UNION UV = 1..Len(seq0)
               /\ \A I, J \in UV : I # J => RelSorted(I, J)
               /\ pc' = "Done" /\ UNCHANGED << seq, seq0, U >>
               /\ TypeOK' /\ ((pc = "Done") => U' = {})
               /\ UV' \in DomainPartitions
               /\ seq' \in PermsOf(seq0')
               /\ UNION UV' = 1..Len(seq0')
               /\ \A I, J \in UV' : I # J => RelSorted(I, J)
               BY <3>2
     <2>2. CASE UNCHANGED vars
       <3>1. TypeOK' /\ ((pc = "Done") => U' = {}) /\ UV' \in DomainPartitions
                 /\ seq' \in PermsOf(seq0') /\ UNION UV' = 1..Len(seq0')
                 /\ \A I, J \in UV' : I # J => RelSorted(I, J)
                 BY vars, Inv, TypeOK
     <2>3. QED BY <2>1, <2>2

<1>3. Inv => PCorrect
     <2>1. /\ seq \in PermsOf(seq0)
           /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]
         <3>1. /\ Len(seq) = Len(seq0) /\ Len(seq) \in Nat /\ Len(seq) > 0
               /\ UV = {{i} : i \in 1..Len(seq)}
               /\ {p} \in UV /\ {q} \in UV
               /\ p < q
               /\ RelSorted({p}, {q})
               BY Inv
         <3>2. QED
           BY <3>1, RelSorted
     <2>2. QED BY <2>1, PCorrect

<1>4. QED BY <1>1, <1>2, <1>3
=============================================================================