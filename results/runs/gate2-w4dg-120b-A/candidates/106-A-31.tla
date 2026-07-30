---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxVal, MaxSeq

VARIABLES x, y, s, seq, f, acc, Permutations

vars == <<x, y, s, seq, f, acc, Permutations>>

TypeOK ==
  /\ x \in 0..MaxVal
  /\ y \in 0..MaxVal
  /\ s \in SUBSET (0..MaxVal)
  /\ seq \in Seq(0..MaxVal)
  /\ f \in [0..MaxVal -> 0..MaxVal]
  /\ acc \in 0..MaxVal
  /\ Permutations \subseteq Seq(0..MaxVal)

Init ==
  /\ x = 0
  /\ y = 0
  /\ s = {}
  /\ seq = << >>
  /\ f = [n \in 0..MaxVal |-> 0]
  /\ acc = 0
  /\ Permutations = {}

\* Operator (1): test whether two sets overlap
Overlap(a, b) == \E z \in a : z \in b

\* Operators (2): maximum and minimum element selection from a set
SetMax(t) == IF t = {} THEN 0 ELSE CHOOSE z \in t : \A w \in t : w <= z
SetMin(t) == IF t = {} THEN 0 ELSE CHOOSE z \in t : \A w \in t : w >= z

\* Operator (3): generalized set reduction (fold over a set with an accumulator)
SetReduce(t) ==
  LET g[S \in SUBSET t] ==
    IF S = {} THEN 0
    ELSE LET z == CHOOSE e \in S : TRUE
         IN f[z] + g[S \ {z}]
  IN g[t]

\* Operator (4): sequence reduction using the library fold operator
SeqReduce ==
  IF seq = << >> THEN 0
  ELSE FoldL(f, seq)

\* Operator (5): find the index of an element in a sequence
IndexOf(seq, e) ==
  LET g[i \in 1..Len(seq)] ==
    IF seq[i] = e THEN i
    ELSE IF i = Len(seq) THEN 0
    ELSE g[i + 1]
  IN g[1]

\* Operator (6): convert a sequence to the set of its elements
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* Operator (7): get the last element of a sequence
Last(seq) == IF seq = << >> THEN 0 ELSE seq[Len(seq)]

\* Operator (8): test if a sequence is empty
IsSeqEmpty(seq) == seq = << >>

\* Operator (9): remove all occurrences of an element from a sequence
RemoveAll(seq, e) ==
  IF seq = << >> THEN << >>
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
  ELSE << Head(seq) >> \o RemoveAll(Tail(seq), e)

\* Operator (10): compute the intersection of a set of sets
SetIntersection(S) ==
  LET g[T \subseteq S] ==
    IF T = {} THEN 0..MaxVal
    ELSE LET z == CHOOSE e \in T : TRUE
         IN z \cap g[T \ {z}]
  IN g[S]

\* Operator (11): generate all permutation sequences of a finite set
PermutationsOf(t) ==
  IF t = {} THEN {<< >>}
  ELSE
    UNION { [<< e >> \o p \in PermutationsOf(t \ {e})] : e \in t }

\* Operator (12): test helper that prints diagnostic info on failure
Assert(expr, msg) == IF expr THEN TRUE ELSE (Print(msg); FALSE)

Spec == Init

====