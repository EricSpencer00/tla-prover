---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokers[i] maps each ingredient to the smoker who has an infinite supply
\* of it; smoking[k] says whether that smoker is currently smoking.
VARIABLES smokers, smoking, offer, lastSmoked

vars == <<smokers, smoking, offer, lastSmoked>>

AllIngredients == {* x \in smokers : x.title *}

TypeOK ==
  /\ smokers \in [Ingredients -> {"matches", "paper", "tobacco"}]
  /\ smoking \in [smokers -> BOOLEAN]
  /\ offer \subseteq Ingredients
  /\ lastSmoked \in {"none", "matches", "paper", "tobacco"}

Init ==
  /\ smoking = [k \in smokers |-> FALSE]
  /\ \E o \in Offers : offer = o
  /\ lastSmoked = "none"

SomeOneSmokes == \E k \in smokers : smoking[k]

\* The dealer offers exactly one missing ingredient; a smoker completes the
\* set and is allowed to burn. The offer is cleared once smoking starts.
StartSmoking ==
  /\ offer # {}
  /\ \E k \in smokers :
       /\ AllIngredients \cup offer = Ingredients
       /\ ~SomeOneSmokes
       /\ smoking' = [smoking EXCEPT ![k] = TRUE]
       /\ lastSmoked' = k.title
  /\ offer' = {}
  /\ UNCHANGED smokers

StopSmoking ==
  /\ SomeOneSmokes
  /\ \E k \in smokers :
       /\ smoking[k]
       /\ smoking' = [smoking EXCEPT ![k] = FALSE]
  /\ \E o \in Offers : offer' = o
  /\ UNCHANGED <<smokers, lastSmoked>>

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne == \A a, b \in smokers : (smoking[a] /\ smoking[b]) => a = b

\* Progress: every smoker that is lit eventually goes out.
Progress == SomeOneSmokes ~> ~SomeOneSmokes

====