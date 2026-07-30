---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANTS
    Ingredients,
    Offers

VARIABLES
    smoking,
    offer

vars == <<smoking, offer>>

Smokers == Ingredients

OfferValid(wo) ==
    /\ wo # {}
    /\ \A i \in Ingredients : i \notin wo => Cardinality(Ingredients) - Cardinality(wo) = 1

TypeOK ==
    /\ smoking \in [Smokers -> BOOLEAN]
    /\ offer \in (Offers \cup {Offers})

Init ==
    /\ smoking = [s \in Smokers |-> FALSE]
    /\ \E wo \in Offers :
         /\ OfferValid(wo)
         /\ offer' = wo
    /\ UNCHANGED smoking

Start ==
    /\ offer # {}
    /\ \E s \in Smokers :
         /\ ~smoking[s]
         /\ offer \cup {s} = Ingredients
         /\ smoking' = [smoking EXCEPT ![s] = TRUE]
    /\ offer' = {}

Stop ==
    /\ offer = {}
    /\ \E s \in Smokers :
         /\ smoking[s]
         /\ smoking' = [smoking EXCEPT ![s] = FALSE]
    /\ \E wo \in Offers :
         /\ OfferValid(wo)
         /\ offer' = wo

Next == Start \/ Stop

AtMostOne ==
    \A a \in Smokers, b \in Smokers :
        (smoking[a] /\ smoking[b]) => a = b

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

====