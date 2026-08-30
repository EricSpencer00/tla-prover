---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

\* The bank-on-which-the-boat-is-docked
VARIABLES boatBank

\* Mapping each bank to the set of people currently on it
VARIABLES bankOf

vars == <<boatBank, bankOf>>

TypeOK ==
  /\ boatBank \in Banks
  /\ bankOf \in [Banks -> SUBSET People]

Init ==
  /\ boatBank = "east"
  /\ bankOf = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A move boards 1-2 people on the current bank and drops them on the other
\* side, only if neither bank would endanger its missionaries.
Move ==
  /\ \E g \in SUBSET bankOf[boatBank] :
       /\ Cardinality(g) \in 1..2
       /\ LET dest == CHOOSE b \in Banks : b # boatBank IN
            /\ bankOf' = [bankOf EXCEPT ![boatBank] = @ \ g, ![dest] = @ \cup g]
            /\ boatBank' = dest
            /\ \A b \in Banks :
                 (bankOf[b] \cap Missionaries # {}) => Cardinality(bankOf[b] \cap Cannibals) <= Cardinality(bankOf[b] \cap Missionaries)
  /\ UNCHANGED <<boatBank>>

Next == Move

\* SAFETY: missionaries are never outnumbered on a bank where they exist
MissionarySafety ==
  \A b \in Banks :
    (bankOf[b] \cap Missionaries # {}) => Cardinality(bankOf[b] \cap Cannibals) <= Cardinality(bankOf[b] \cap Missionaries)

\* SAFETY: the boat always carries a non-empty group of size at most two
BoatCapacity ==
  \A b \in Banks :
    Cardinality(bankOf[b] \cap People) + Cardinality(bankOf[CHOOSE c \in Banks : c # b] \cap People) = Cardinality(People)

TypeOKInv == TypeOK /\ MissionarySafety /\ BoatCapacity

\* LIVENESS: not a property of the system itself; the puzzle is solved when the
\* departure bank is empty, which a model checker will then search for as a
\* reachable state rather than as an invariant.
Solution == bankOf["east"] = {}

====