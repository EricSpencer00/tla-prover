---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boatBank, bankPeople

vars == <<boatBank, bankPeople>>

EastBank == "east"
WestBank == "west"
Banks == {EastBank, WestBank}

Both == Missionaries \cup Cannibals

\* The boat's capacity is just not a single person, so it never travels
\* empty and never carries more than two.
Cap == {1, 2}

PeopleOn(people, bank) == Cardinality({z \in people : bankPeople[bank] \ni z})

TypeOK ==
    /\ boatBank \in Banks
    /\ bankPeople \in [Banks -> SUBSET Both]

AtLeastOnePerson == (\E bank \in Banks : bankPeople[bank] # {})
AtMostTwoPeople == (\A bank \in Banks : PeopleOn(bankPeople[bank], bank) <= 2)

\* A bank is safe if it either has no missionaries at all or the cannibals
\* there do not outnumber them.
BankSafe(bank) ==
    bankPeople[bank] \cap Missionaries = {} \/ PeopleOn(bankPeople[bank] \cap Cannibals, bank) <= PeopleOn(bankPeople[bank] \cap Missionaries, bank)

SafeBanks ==
    /\ BankSafe(EastBank)
    /\ BankSafe(WestBank)

\* The boat crosses with exactly the people described by the move's scope;
\* the capacity constraint (Cap = 0) is what stops it being empty.
Move ==
    /\ AtLeastOnePerson
    /\ AtMostTwoPeople
    /\ SafeBanks
    /\ \E src \in Banks, dst \in Banks :
         /\ src # dst
         /\ boatBank = src
         /\ \E occ \in [Both -> BOOLEAN] :
              /\ Cardinality({z \in Both : occ[z]}) \in Cap
              /\ bankPeople' = [bankPeople EXCEPT ![src] = bankPeople[src] \ {z \in Both : occ[z]}, ![dst] = bankPeople[dst] \cup {z \in Both : occ[z]}]
         /\ boatBank' = dst

Next == Move

Init ==
    /\ boatBank = EastBank
    /\ bankPeople = [bank \in Banks |-> IF bank = EastBank THEN Both ELSE {}]

\* A solution is found once the east bank is empty (all have crossed safely).
Solution == EastBank \notin {bank \in Banks : bankPeople[bank] # {}}

Spec == Init /\ [][Next]_vars

====