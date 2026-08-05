---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \subseteq Ingredients

Init ==
    /\ \A ig \in Ingredients : smoking[ig] = FALSE
    /\ \E o \in Offers : offer = o

Light ==
    /\ offer # {}
    /\ \E ig \in Ingredients :
         /\ Cardinality(offer \cup {ig}) = Cardinality(Ingredients)
         /\ smoking' = [smoking EXCEPT ![ig] = TRUE]
    /\ offer' = {}

Finish ==
    /\ offer = {}
    /\ \E ig \in Ingredients :
         /\ smoking[ig]
         /\ smoking' = [smoking EXCEPT ![ig] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == Light \/ Finish

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A ig1 \in Ingredients, ig2 \in Ingredients :
        (smoking[ig1] /\ smoking[ig2]) => ig1 = ig2

====