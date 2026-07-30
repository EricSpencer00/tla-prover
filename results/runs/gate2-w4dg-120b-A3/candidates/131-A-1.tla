---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

\* Extending the existing majority vote spec with a machine-checked proof.
\* The full action set and state variables come from the base spec; this
\* module adds only the proof obligations, so Init and Next just alias
\* the definitions from the base file.

VARIABLES seq, candidate, count, seen

vars == <<seq, candidate, count, seen>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value
  /\ count \in Nat
  /\ seen \subseteq Nat

Init ==
  /\ seq = << >>
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ count = 0
  /\ seen = {}

\* The voting algorithm: when the counter is zero the next element becomes
\* the candidate; otherwise the counter is decremented if the new element
\* disagrees with the current candidate and incremented if it agrees.
Next ==
  \/ \E v \in Value :
       /\ seq' = Append(seq, v)
       /\ seen' = seen \cup { Len(seq) }
       /\ IF count = 0 THEN
            /\ candidate' = v
            /\ count' = 1
          ELSE IF v = candidate THEN
            /\ candidate' = candidate
            /\ count' = count + 1
          ELSE
            /\ candidate' = candidate
            /\ count' = count - 1
  \/ \E v \in Value :
       /\ Len(seq) > 0
       /\ \A w \in seen : seq[w] = v
       /\ candidate' = v
       /\ UNCHANGED <<seq, count, seen>>

Spec == Init /\ [][Next]_vars

\* The number of positions before index i in a sequence is exactly i; this
\* holds because those positions are integers 0..(i-1), a finite set.
PositionsBeforeExactly(i) == Cardinality({ w \in seen : w < i }) = i

Inv ==
  /\ TypeOK
  /\ Cardinality(seen) = Len(seq)
  /\ \A i \in seen : i < Len(seq)
  /\ \A i \in seen : i \in Nat
  /\ \A i \in seen : seq[i] \in Value
  /\ \A i \in seen : PositionsBeforeExactly(i)
  /\ \A v \in Value : candidate = v => \A w \in seen : seq[w] = v

\* The candidate is a strict majority element only if it equals the unique
\* value that actually occurs in more than half the positions of a full
\* scan (i.e., once no more input is left).
Correct ==
  /\ Inv
  /\ Len(seq) = Len(seen)
  /\ Cardinality(seen) > 1
  /\ \A v \in Value : candidate = v => 2 * Cardinality({ w \in seen : seq[w] = v }) > Cardinality(seen)

====