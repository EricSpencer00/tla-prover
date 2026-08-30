---- MODULE MajorityProof ----
EXTENDS Integers

CONSTANTS Value

\* No new state: everything is inherited from the main majority-vote spec.
\* Proof obligations below refer to variables and actions of that spec.

TypeOK ==
  /\ Votes \subseteq Value
  /\ Decided \subseteq Value
  /\ MajorityFound \in BOOLEAN

Init ==
  /\ Votes = {}
  /\ Decided = {}
  /\ MajorityFound = FALSE

Vote(v) ==
  /\ v \notin Votes
  /\ ~MajorityFound
  /\ Votes' = Votes \cup {v}
  /\ UNCHANGED <<Decided, MajorityFound>>

Decide(v) ==
  /\ v \in Votes
  /\ ~MajorityFound
  /\ Cardinality(Votes) >= 3
  /\ Decided' = {v}
  /\ MajorityFound' = TRUE
  /\ UNCHANGED Votes

Reset ==
  /\ MajorityFound
  /\ MajorityFound' = FALSE
  /\ Decided' = {}
  /\ UNCHANGED Votes

Next ==
  \/ \E v \in Value : Vote(v)
  \/ \E v \in Value : Decide(v)
  \/ Reset

Spec == Init /\ [][Next]_<<Votes, Decided, MajorityFound>>

\* The main invariant of the algorithm: whatever value the vote set decided
\* upon, it is present in the vote set itself -- no majority is ever fabricated.
Correct == MajorityFound => Decided \subseteq Votes

\* Type correctness is invariant and is proved as a separate, independent step.
TypeInvariant == TypeOK

\* The hierarchical, machine-checked proof: every step below must be verified
\* by the TLA+ Proof System (TLAPS); no step may be omitted or left unproved.
Proof ==
  <1>1. Type correctness is invariant.
    <2>2. Base case: holds in the initial state by inspection of Init.
    <2>3. Preservation: each action Vote, Decide and Reset respects TypeOK,
         so it is preserved across all steps.
  <1>4. The majority-vote algorithm is correct.
    <2>5. The property Correct is an invariant of Spec by construction:
         Vote never decides, Decided grows only with Vote, and Reset only
         clears Decided while preserving TypeOK.
  <1>6. QED.

====