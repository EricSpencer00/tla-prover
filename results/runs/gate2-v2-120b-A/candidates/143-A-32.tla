---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

\* The two possible banks
Banks == {"east", "west"}

\* Variables:
VARIABLES boat, people

\* Helper definitions
MissionariesOn(b) == { p \in people[b] : p \in Missionaries }
CannibalsOn(b)   == { p \in people[b] : p \in Cannibals }

\* Safety predicate for a single bank
BankSafe(b) ==
  /\ (MissionariesOn(b) = {})          \* no missionaries, trivially safe
  \/ (Cardinality(CannibalsOn(b)) <= Cardinality(MissionariesOn(b)))

\* Global safety predicate (used for invariant)
StateSafe == /\ BankSafe("east")
             /\ BankSafe("west")

\* Initial state: everyone on east bank, boat on east
Init ==
  /\ boat = "east"
  /\ people = [b \in Banks |-> IF b = "east"
                               THEN Missionaries \cup Cannibals
                               ELSE {}]

\* A move consists of selecting 1 or 2 distinct people from the current bank,
\* moving them to the opposite bank, and updating the boat location.
Move ==
  /\ \E grp \subseteq people[boat] :
        /\ Cardinality(grp) \in {1, 2}
        /\ LET dest == IF boat = "east" THEN "west" ELSE "east" IN
           /\ people' = [b \in Banks |-> 
                         IF b = boat   THEN people[b] \ SetMinus grp
                         ELSE IF b = dest THEN people[b] \cup grp
                         ELSE people[b]]
           /\ boat'   = dest
  /\ StateSafe   \* resulting state must be safe on both banks

\* Stuttering step to avoid deadlock when the goal is reached
Stutter ==
  /\ boat = boat
  /\ people = people

Next == Move \/ Stutter

\* Type correctness invariant: the variables always contain people from the
\* declared sets and the boat always points to a legal bank.
TypeOK ==
  /\ boat \in Banks
  /\ people \in [Banks -> SUBSET Missionaries \cup Cannibals]
  /\ people["east"] \cup people["west"] = Missionaries \cup Cannibals
  /\ people["east"] \cap people["west"] = {}

\* Solution invariant: the east bank is never empty (a violation indicates a
\* successful crossing).
Solution == people["east"] # {}

\* Specification (optional, not required by the .cfg but customary)
Spec == Init /\ [][Next]_<<boat, people>>

====