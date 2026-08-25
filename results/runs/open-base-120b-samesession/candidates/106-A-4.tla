---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Set intersection test (whether two sets overlap)
\* ----------------------------------------------------------------------
SetOverlap(S, T) == S \cap T # {}

\* ----------------------------------------------------------------------
\* Maximum and minimum element selection from a set
\* ----------------------------------------------------------------------
SetMax(S) == 
  IF S = {} THEN 
    Print("SetMax called on empty set") /\ FALSE
  ELSE 
    CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) == 
  IF S = {} THEN 
    Print("SetMin called on empty set") /\ FALSE
  ELSE 
    CHOOSE x \in S : \A y \in S : y >= x

\* ----------------------------------------------------------------------
\* Generalized set reduction (fold over a set with an accumulator)
\* The operator `op` must be a two‑argument operator: op[element, acc]
\* ----------------------------------------------------------------------
SetFold(S, init, op) ==
  IF S = {} THEN 
    init
  ELSE 
    LET x == CHOOSE e \in S : TRUE
    IN op[x, SetFold(S \ {x}, init, op)]

\* ----------------------------------------------------------------------
\* Sequence reduction (fold over a sequence with an accumulator)
\* The operator `op` must be a two‑argument operator: op[element, acc]
\* ----------------------------------------------------------------------
SeqFold(seq, init, op) ==
  IF Len(seq) = 0 THEN
    init
  ELSE
    op[Head(seq), SeqFold(Tail(seq), init, op)]

\* ----------------------------------------------------------------------
\* Finding the index of an element in a sequence (1‑based, 0 if absent)
\* ----------------------------------------------------------------------
SeqIndex(seq, elem) ==
  IF elem \in SeqSet(seq) THEN
    CHOOSE i \in DOMAIN seq : seq[i] = elem
  ELSE
    0

\* ----------------------------------------------------------------------
\* Converting a sequence to the set of its elements
\* ----------------------------------------------------------------------
SeqSet(seq) == { seq[i] : i \in DOMAIN seq }

\* ----------------------------------------------------------------------
\* Getting the last element of a sequence (undefined for empty sequences)
\* ----------------------------------------------------------------------
SeqLast(seq) ==
  IF Len(seq) = 0 THEN
    Print("SeqLast called on empty sequence") /\ FALSE
  ELSE
    seq[Len(seq)]

\* ----------------------------------------------------------------------
\* Testing if a sequence is empty
\* ----------------------------------------------------------------------
SeqIsEmpty(seq) == Len(seq) = 0

\* ----------------------------------------------------------------------
\* Removing all occurrences of an element from a sequence
\* ----------------------------------------------------------------------
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE IF Head(seq) = elem THEN
    SeqRemoveAll(Tail(seq), elem)
  ELSE
    <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* ----------------------------------------------------------------------
\* Intersection of a set of sets
\* ----------------------------------------------------------------------
SetIntersection(SS) ==
  { x : \A S \in SS : x \in S }

\* ----------------------------------------------------------------------
\* Generating all permutation sequences of a finite set
\* ----------------------------------------------------------------------
Permutations(S) ==
  IF S = {} THEN
    { <<>> }
  ELSE
    UNION {
      <<x>> \o p :
        x \in S,
        p \in Permutations(S \ {x})
    }

\* ----------------------------------------------------------------------
\* Test helper for writing assertions that print diagnostic information on failure
\* ----------------------------------------------------------------------
Assert(p, msg) ==
  IF p THEN TRUE ELSE Print(msg) /\ FALSE

====