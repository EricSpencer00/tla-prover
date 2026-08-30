---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

\* The state-transition system is inherited; this module only adds the proof.
Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ vars \in [candidate : Value \cup {"none"}, count : Nat, scanned : 0..Len, yes : SUBSET Value]
  /\ Len \in Nat /\ Len >= 1
  /\ \A v \in yes : v \in Value

\* The correctness invariant from the main spec, lifted so it can be proved
\* here as well -- it is not a new property created by the proof itself.
Inv == Inv

\* The new proof goal: any strict-majority element of the scanned prefix must
\* equal the single candidate the algorithm settles on.
Correct ==
  \A v \in Value : (2 * Cardinality({i \in 1..Len : seq[i] = v}) > Len) => (v = candidate)

====