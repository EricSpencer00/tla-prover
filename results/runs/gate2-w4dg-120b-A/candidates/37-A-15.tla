---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* smoking[g] is the smoker's own flag (true iff the smoker holding ingredient g is smoking).
VARIABLES smoking, offer

vars == <<smoking, offer>>

Complete == Ingredients

Init == /\ smoking = [g \in Ingredients |-> FALSE]
        /\ \E o \in Offers : offer = o

\* A smoker is ready when the offer, plus that smoker's own ingredient, covers everything.
Ready(g) == offer # {} /\ (offer \cup {g}) = Complete
SmokingCount == Cardinality({g \in Ingredients : smoking[g]})

Start(g) == /\ Ready(g)
            /\ ~smoking[g]
            /\ SmokingCount = 0
            /\ smoking' = [smoking EXCEPT ![g] = TRUE]
            /\ offer' = {}
            /\ UNCHANGED <<>>

\* The empty offer means a smoker is currently smoking; it changes on Stop.
Stop(g) == /\ smoking[g]
           /\ smoking' = [smoking EXCEPT ![g] = FALSE]
           /\ \E o \in Offers : offer' = o
           /\ UNCHANGED <<>>

Next == (\E g \in Ingredients : Start(g)) \/ (\E g \in Ingredients : Stop(g))
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E g \in Ingredients : Start(g))
        /\ WF_vars(\E g \in Ingredients : Stop(g))

TypeOK == /\ smoking \in [Ingredients -> BOOLEAN]
          /\ offer \in Offers

\* Bounded capacity: the number of smokers smoking is a natural number <= 1.
AtMostOne == SmokingCount <= 1

====