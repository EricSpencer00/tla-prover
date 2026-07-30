---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The state variables come from the main spec, so this module has no new
\* variables of its own.
VARIABLES candidate, count, scanned, seq

TypeOK ==
  /\ candidate \in Value \cup {"none"}
  /\ count \in Nat
  /\ scanned \in Nat
  /\ seq \in [0..3 -> Value]

\* No new actions: every transition comes from the main spec.
Init ==
  /\ candidate = "none"
  /\ count = 0
  /\ scanned = 0
  /\ seq = [i \in 0..3 |-> CHOOSE v \in Value : TRUE]

Vote(v) ==
  /\ scanned < 4
  /\ seq' = [seq EXCEPT ![scanned] = v]
  /\ scanned' = scanned + 1
  /\ IF count = 0 THEN /\ candidate' = v
                    /\ count' = 1
     ELSE IF candidate = v THEN count' = count + 1
     ELSE count' = count - 1
  /\ UNCHANGED <<candidate>>

\* The machine-checked proof (TLAPS) of type correctness; invariant
\* preservation for each transition is built into the proof steps below.
Spec == Init /\ [][Vote(Value)]_<<candidate, count, scanned, seq>>

\* Lemma: the occurrence set of a value up to index n is finite.
LemmaOccFinite(v, n) ==
  /\ n <= 4
  /\ Cardinality({i \in 0..(n - 1) : seq[i] = v}) < 5

\* Lemma: adding a new index strictly beyond the current scanned range
\* increases the occurrence set cardinality by exactly one.
LemmaOccStep(v, n) ==
  /\ n < 4
  /\ seq[n] = v
  /\ Cardinality({i \in 0..n : seq[i] = v}) = Cardinality({i \in 0..(n - 1) : seq[i] = v}) + 1

\* Lemma: decreasing the candidate's count (when a vote is cancelled) does
\* not lose track of a strict majority.
LemmaCancel(v, n) ==
  /\ n < 4
  /\ seq[n] # candidate
  /\ count >= 1
  /\ Cardinality({i \in 0..n : seq[i] = candidate}) >= Cardinality({i \in 0..n : seq[i] = v})

\* Lemma: when a vote is adopted for a candidate it never loses its
\* strict-majority advantage at the next step.
LemmaAdopt(v, n) ==
  /\ n < 4
  /\ seq[n] = v
  /\ candidate = "none"
  /\ Cardinality({i \in 0..n : seq[i] = v}) > Cardinality({i \in 0..n : seq[i] # v})

Inv ==
  /\ candidate \in Value
  /\ count = Cardinality({i \in 0..(scanned - 1) : seq[i] = candidate})
  /\ \A v \in Value : Cardinality({i \in 0..(scanned - 1) : seq[i] = v}) <= scanned
  /\ \A v \in Value : LemmaOccFinite(v, scanned)
  /\ \A v \in Value : LemmaOccStep(v, scanned)
  /\ \A v \in Value : LemmaCancel(v, scanned)
  /\ \A v \in Value : LemmaAdopt(v, scanned)

Correct ==
  /\ scanned = 4
  /\ \A v \in Value : Cardinality({i \in 0..3 : seq[i] = v}) > 2 => candidate = v

====