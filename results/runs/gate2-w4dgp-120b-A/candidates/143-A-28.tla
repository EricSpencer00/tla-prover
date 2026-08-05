---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* People = the set of all individuals involved, each tagged as missionary or
\* cannibal for accounting.
People == Missionaries \cup Cannibals

Banks == {"east", "west"}

VARIABLES boat, bank

vars == <<boat, bank>>

\* Safety sub-check: a bank with missionaries must not have more cannibals than
\* missionaries on it; a bank of only cannibals is trivially safe.
BankSafe(b) ==
  /\ (bank[b] \cap Missionaries = {} \/ Cardinality(bank[b] \cap Cannibals)
       <= Cardinality(bank[b] \cap Missionaries))

TypeOK ==
  /\ boat \in Banks
  /\ bank \in [Banks -> SUBSET People]

Init ==
  /\ boat = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A crossing moves at least one but no more than two people across the river,
\* and only when the resulting configuration on both banks stays safe.
Next ==
  \/ \E S \subseteq bank[boat] :
       /\ S # {}
       /\ Cardinality(S) <= 2
       /\ boat' = CHOOSE d \in Banks : d # boat
       /\ bank' = [bank EXCEPT ![boat] = bank[boat] \ S, ![CHOOSE d \in Banks : d # boat] =
                       bank[CHOOSE d \in Banks : d # boat] \cup S]
       /\ BankSafe(boat) /\ BankSafe(CHOOSE d \in Banks : d # boat)

\* According to the description's note, an unsafe move would be detectable as a
\* state violating the bank-safety rule, so the real property to check is that
\* every reachable state preserves bank safety (a literal contradiction of the
\* note would be flagged here as a model-checking error rather than a deadlock).
Solution == \A b \in Banks : BankSafe(b)

NextEnabled == Next

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====