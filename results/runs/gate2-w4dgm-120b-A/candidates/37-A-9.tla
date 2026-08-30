---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokerOn[i] is the smoking flag of the (unique) smoker holding infinite
\* supply of ingredient i; offer is the dealer's current table offer.
VARIABLES smokerOn, offer

vars == <<smokerOn, offer>>

TypeOK ==
    /\ smokerOn \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

Init ==
    /\ smokerOn = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* A smoker may only join when its own ingredient completes the full set.
CanSmoke(i) ==
    offer # {} /\ offer \cup {i} = Ingredients /\ ~smokerOn[i]

SomeSmoking == \E i \in Ingredients : smokerOn[i]

StartSmoke(i) ==
    /\ CanSmoke(i)
    /\ smokerOn' = [smokerOn EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoke(i) ==
    /\ smokerOn[i]
    /\ smokerOn' = [smokerOn EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next ==
    \E i \in Ingredients : StartSmoke(i) \/ StopSmoke(i)

\* Every smoker that is smoking is the unique smoker of its own unique
\* ingredient, so smoking smokers can never be more than one.
AtMostOne == SomeSmoking => (\E i \in Ingredients : smokerOn[i])

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A i \in Ingredients : WF_vars(StartSmoke(i)) /\ WF_vars(StopSmoke(i))
    /\ AtMostOne

TypeOKInv == TypeOK
====