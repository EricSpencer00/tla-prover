---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

Bank == {0, 1}
MaxPassengers == 2

VARIABLES boat, bankPeople

vars == <<boat, bankPeople>>

People == Missionaries \cup Cannibals

TypeOK ==
  /\ boat \in Bank
  /\ bankPeople \in [Bank -> SUBSET People]

\* On each bank, either no missionaries are present, or cannibals do not outnumber them.
BankSafe ==
  \A b \in Bank :
    LET m == Cardinality(bankPeople[b] \cap Missionaries)
        c == Cardinality(bankPeople[b] \cap Cannibals)
    IN m = 0 \/ c <= m

Init ==
  /\ boat = 0
  /\ bankPeople = [b \in Bank |-> IF b = 0 THEN Missionaries \cup Cannibals ELSE {}]

\* Moving a non-empty group of at most two people from the current bank to the other
\* is only allowed if the post-move distribution is safe on both banks.
Next ==
  \/ \E G \in SUBSET bankPeople[boat] :
       /\ G # {}
       /\ Cardinality(G) <= MaxPassengers
       /\ LET otherBank == 1 - boat IN
            /\ \A b \in Bank :
                 LET pps == IF b = boat THEN bankPeople[boat] \ G ELSE IF b = otherBank THEN bankPeople[otherBank] \cup G ELSE {}
                     m == Cardinality(pps \cap Missionaries)
                     c == Cardinality(pps \cap Cannibals)
                 IN m = 0 \/ c <= m
            /\ bankPeople' = [b \in Bank |
                               IF b = boat THEN bankPeople[boat] \ G
                               ELSE IF b = otherBank THEN bankPeople[otherBank] \cup G
                               ELSE bankPeople[b]]
            /\ boat' = otherBank
       )
  \/ UNCHANGED vars

Solution == bankPeople[0] # {}

Spec == Init /\ [][Next]_vars

====