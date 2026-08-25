---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS 
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* the faded color
    MeetingPlaceEmpty

\* Colors
CONSTANT Blue, Red, Yellow

Color == {Blue, Red, Yellow, Faded}

\* State variables
VARIABLES 
    creatures,   \* [i \in 1..N |-> [color : Color, meetCount : Nat]]
    mall,        \* either MeetingPlaceEmpty or a creature identifier
    total        \* total number of meetings performed

\* Helper definitions
vars == <<creatures, mall, total>>

\* Complement rule for two colors
Complement(c1, c2) ==
    CASE c1 = c2 -> c1
    [] (c1 = Blue /\ c2 = Red) \/ (c1 = Red /\ c2 = Blue) -> Yellow
    [] (c1 = Blue /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) -> Red
    [] (c1 = Red /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red) -> Blue

\* Initial state
Init ==
    /\ creatures \in [1..N -> [color : Color, meetCount : Nat]]
    /\ \A i \in 1..N: /\ creatures[i].color \in {Blue, Red, Yellow}
                      /\ creatures[i].meetCount = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* Action: a non‑faded creature enters an empty mall (while meetings still allowed)
Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in 1..N :
          /\ creatures[c].color # Faded
          /\ mall' = c
          /\ UNCHANGED <<creatures, total>>
    /\ UNCHANGED total

\* Action: after the limit is reached, a creature that tries to enter fades out
FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E c \in 1..N :
          /\ creatures[c].color # Faded
          /\ creatures' = [creatures EXCEPT ![c].color = Faded]
          /\ UNCHANGED <<mall, total>>

\* Action: a second creature arrives and a meeting takes place
Meet ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E c_wait \in 1..N, c_arr \in 1..N :
          /\ mall = c_wait
          /\ c_arr # c_wait
          /\ creatures[c_arr].color # Faded
          /\ LET newCol == Complement(creatures[c_wait].color,
                                      creatures[c_arr].color) IN
                /\ creatures' = [creatures EXCEPT
                                   ![c_wait] = [color |-> newCol,
                                                meetCount |-> creatures[c_wait].meetCount + 1],
                                   ![c_arr] = [color |-> newCol,
                                                meetCount |-> creatures[c_arr].meetCount + 1]]
                /\ mall' = MeetingPlaceEmpty
                /\ total' = total + 1

\* Next-state relation
Next == Enter \/ FadeOut \/ Meet

\* Specification
Spec == Init /\ [][Next]_vars

\* Type correctness invariant
TypeOK ==
    /\ creatures \in [1..N -> [color : Color, meetCount : Nat]]
    /\ \A i \in 1..N:
          /\ creatures[i].color \in Color
          /\ creatures[i].meetCount \in Nat
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M

\* Safety invariant: sum of individual meeting counts equals twice the total meetings when limit reached
SumMet ==
    (total = M) => (∑ i \in 1..N : creatures[i].meetCount) = 2 * M

====