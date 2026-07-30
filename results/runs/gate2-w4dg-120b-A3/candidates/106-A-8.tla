---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxVal, EmptySeq

VARIABLES elems

vars == <<elems>>

TypeOK == /\ elems \in 0..MaxVal
          /\ MaxVal \in Nat
          /\ EmptySeq \in <<>>

Init == elems = 0

Next == /\ elems' = (elems + 1) % (MaxVal + 1)
        /\ UNCHANGED << >>

Spec == Init /\ [][Next]_vars

\* operator: set intersection test (whether two sets overlap)
SetsOverlap == {x \in {"a", "b", "c"} : x = "a"} \cap {x \in {"a", "d"} : TRUE} # {}

\* operator: maximum and minimum element selection from a set
MaxSet == CHOOSE x \in {1, 2, 3} : \A y \in {1, 2, 3} : y <= x
MinSet == CHOOSE x \in {1, 2, 3} : \A y \in {1, 2, 3} : x <= y

\* operator: generalized set reduction (fold over a set with an accumulator)
SetReduce ==
  LET f[S \in SUBSET {1, 2, 3}] == IF S = {} THEN 0
                           ELSE LET x == CHOOSE y \in S : TRUE
                                IN x + f[S \ {x}]
  IN f[{1, 2, 3}]

\* operator: sequence reduction (fold over a sequence) via library foldl
SeqReduce ==
  LET f[S \in Seq({1, 2, 3})] == Foldl((a, b) |-> a + b, 0, S)
  IN f <<1, 2, 3>>

\* operator: finding the index of an element in a sequence
SeqIndex == CHOOSE i \in DOMAIN <<1, 2, 3>> :
              LET S == <<1, 2, 3>> IN S[i] = 2

\* operator: converting a sequence to the set of its elements
SeqToSet == LET S == <<1, 2, 3>> IN {S[i] : i \in DOMAIN S}

\* operator: the last element of a sequence
SeqLast == LET S == <<1, 2, 3>> IN S[Len(S)]

\* operator: testing if a sequence is empty
SeqEmpty == Len(EmptySeq) = 0

\* operator: removing all occurrences of an element from a sequence
SeqRemove == LET S == <<1, 2, 3>> IN SelectSeq(S, LAMBDA x : x # 2)

\* operator: intersecting a set of sets
SetIntersection == {x \in {1, 2, 3} : \A S \in {{1, 2}, {2, 3}} : x \in S}

\* operator: generating all permutation sequences of a finite set
Permutations ==
  {p \in Seq({1, 2, 3}) : Cardinality(RANGE p) = Len(p)}

\* operator: a test helper that prints diagnostic info on failure
AssertTrue ==
  LET x == 5
  IN IF x = 5 THEN TRUE ELSE (Print("x =", x); FALSE)

Spec == Spec
Init == Init
Next == Next

====