---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Colors == {blue, red, yellow, Faded}
PrimaryColors == {blue, red, yellow}

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in PrimaryColors : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Cre, Mall, tot

\* Cre : [1..N -> [color : Colors, meetCount : Nat]]
\* Mall : either MeetingPlaceEmpty or a creature identifier in 1..N
\* tot  : Nat  (total number of completed meetings)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Cre = [i \in 1..N |-> [color |-> CHOOSE c \in PrimaryColors : TRUE,
                              meetCount |-> 0]]
    /\ Mall = MeetingPlaceEmpty
    /\ tot = 0

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature enters an empty meeting place
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ Mall = MeetingPlaceEmpty
    /\ tot < M
    /\ \E i \in 1..N :
          /\ Cre[i].color # Faded
          /\ Mall' = i
          /\ Cre' = Cre
          /\ tot' = tot

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature tries to enter after the limit – it fades out
\* ----------------------------------------------------------------------
FadeOut ==
    /\ Mall = MeetingPlaceEmpty
    /\ tot >= M
    /\ \E i \in 1..N :
          /\ Cre[i].color # Faded
          /\ Cre' = [Cre EXCEPT ![i].color = Faded]
          /\ Mall' = MeetingPlaceEmpty
          /\ tot' = tot

\* ----------------------------------------------------------------------
\* Action: two different non‑faded creatures meet and mutate
\* ----------------------------------------------------------------------
MeetAndMutate ==
    /\ Mall = j
    /\ j \in 1..N
    /\ tot < M
    /\ \E i \in 1..N :
          /\ i # j
          /\ Cre[i].color # Faded
          /\ Cre[j].color # Faded
          /\ LET newc == Complement(Cre[i].color, Cre[j].color) IN
                /\ Cre' = [Cre EXCEPT
                            ![i].color = newc,
                            ![i].meetCount = @ + 1,
                            ![j].color = newc,
                            ![j].meetCount = @ + 1]
                /\ Mall' = MeetingPlaceEmpty
                /\ tot' = tot + 1

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_(<<Cre, Mall, tot>>)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Cre \in [1..N -> [color : Colors, meetCount : Nat]]
    /\ Mall \in {MeetingPlaceEmpty} \cup 1..N
    /\ tot \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: sum of individual meeting counts equals 2*M when tot = M
\* ----------------------------------------------------------------------
SumMet ==
    (tot = M) => 
        ( \* sum over all creatures' meetCount
          LET totalMeetings == 
                Sum({ Cre[i].meetCount : i \in 1..N })
          IN totalMeetings = 2 * M )

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration
\* ----------------------------------------------------------------------
INVARIANTS == { TypeOK, SumMet }

====