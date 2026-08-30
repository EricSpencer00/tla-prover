---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

Intervals == UNION {[i, j] : i, j \in 1..MaxSeqLen}

VARIABLES sequence, original, work, pc
vars == <<sequence, original, work, pc>>

Domain == UNION {1..Len(sequence), Len(sequence) + 1..MaxSeqLen}
DomainOf(s) == UNION {1..n : n \in Domain : Len(s) = n}
\* The permutation definition from the book: defined by composition with a
\* domain automorphism, lifted to sequences.
Automorphisms(s) == {f \in [DomainOf(s) -> DomainOf(s)] :
  \A x \in DomainOf(s), y \in DomainOf(s) : (f[x] = f[y]) => (x = y)}

\* A partition of the whole sequence that leaves everything outside the
\* interval unchanged; the pivot index is the point where it is split.
Partitions(s, i, j) == {t \in [DomainOf(s) -> Values] :
  \A x \in DomainOf(s) :
    IF x < i \/ x > j THEN t[x] = s[x]
    ELSE \E a \in s[i..j] : \A y \in i..j : (y <= x) => (t[y] <= a)}

TypeOK ==
  /\ sequence \in [1..MaxSeqLen -> Values]
  /\ original \in [1..MaxSeqLen -> Values]
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E n \in 1..MaxSeqLen : \E s \in [1..n -> Values] : sequence = s
  /\ original = sequence
  /\ work = {[1, Len(sequence)]}
  /\ pc = "loop"

Loop ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E iv \in work :
       /\ work' = work \ {iv}
       /\ IF iv[1] = iv[2] THEN UNCHANGED <<sequence, work>>
          ELSE \E pivot \in iv[1]..iv[2] :
                 /\ \E t \in Partitions(sequence, iv[1], iv[2]) : sequence' = t
                 /\ work' = work \cup {[iv[1], pivot], [pivot + 1, iv[2]]}
  /\ pc' = pc

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<sequence, original, work>>

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next = Loop \/ Terminate \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

\* Sortedness is not a plain universal property: every interval that was ever
\* present in the work set must appear sorted in the final sequence.
DomainSorted(s) == \A i, j \in DomainOf(s) : i < j => s[i] <= s[j]

Inv ==
  /\ (\A iv \in work : \E x \in 1..Len(sequence) : iv = [1, x]) \/ (\A iv \in work : iv[1] <= iv[2])
  /\ (\A iv \in work : {sequence[x] : x \in iv[1]..iv[2]} = {original[x] : x \in iv[1]..iv[2]})
  /\ (\A iv \in work : \A x, y \in iv[1]..iv[2] : x <= y => sequence[x] <= sequence[y])
  /\ (\A iv \in work : \A x \in iv[1]..iv[2] : \E y \in iv[1]..iv[2] : original[y] = sequence[x])

PCorrect == pc = "done" => (\A x \in Domain : \E f \in Automorphisms(original) : original[f[x]] = sequence[x] /\ DomainSorted(sequence))

Termination == <> (pc = "done")

====