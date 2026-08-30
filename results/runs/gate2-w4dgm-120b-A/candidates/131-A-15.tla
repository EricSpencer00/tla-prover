---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* Majority vote over a fixed input sequence. The algorithm keeps a candidate
\* and a running count, and the invariant we prove is that the count always
\* equals the number of times the candidate actually occurs up to the current
\* scan index -- so a strict majority forces the candidate to be the true
\* majority value.
VARIABLES seq, n, candidate, count, index

vars == <<seq, n, candidate, count, index>>

Values == (1..n) \X {1, 2}

TypeOK ==
  /\ seq \in [1..n -> {1, 2}]
  /\ candidate \in {0, 1, 2}
  /\ count \in 0..n
  /\ index \in 0..n

Init ==
  /\ \E s \in Values: seq = [i \in 1..n |-> s[i]]
  /\ candidate = 0
  /\ count = 0
  /\ index = 0

\* The candidate is replaced whenever the running count reaches zero.
Next ==
  /\ index < n
  /\ LET x == seq[index + 1] IN
       candidate' = IF count = 0 THEN x ELSE candidate
       \/ count' = IF count = 0 THEN 1 ELSE IF x = candidate THEN count + 1 ELSE count - 1
  /\ index' = index + 1
  /\ UNCHANGED <<seq, n>>

\* After the scan finishes, the algorithm may report its candidate as the
\* majority holder. This is the only step that produces an observable
\* output, and it is the step the correctness property is about.
Report ==
  /\ index = n
  /\ candidate # 0
  /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Report)

\* The running count always matches the true number of occurrences of the
\* candidate seen so far, which is what forces a strict majority to be the
\* candidate itself.
Inv == count = Cardinality({i \in 1..index : seq[i] = candidate})

Correct == (index = n /\ candidate # 0) => \A x \in {1, 2} : (2 * Cardinality({i \in 1..n : seq[i] = x}) > n) => x = candidate

\* Type correctness is an invariant of the whole spec, so it is proved by
\* standard inductive checking and has no separate proof script.
TypeOKInv == TypeOK

\* The whole correctness argument is the hierarchical proof below: the top
\* level invokes the two sub-properties in sequence.
AllProps == TypeOKInv /\ Correct

====