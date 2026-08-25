---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Primary colors
PrimaryColors == {"blue", "red", "yellow"}

\* All possible colors (including faded)
Colors == PrimaryColors \cup {Faded}

VARIABLES creatures, mall, total

\* ----------------------------------------------------------------------
\* Complement rule: given two non‑faded colors, returns the new color
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CASE 
            (c1 = "blue"  /\ c2 = "red")    \/ (c1 = "red"    /\ c2 = "blue")    -> "yellow" ;
            (c1 = "blue"  /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue")   -> "red" ;
            (c1 = "red"   /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "red")    -> "blue"
        END

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ creatures = [i \in 1..N |-> [color |-> CHOOSE c \in PrimaryColors: TRUE,
                                      count |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* An unfaded creature enters an empty meeting place (if the limit not reached)
\* ----------------------------------------------------------------------
Enter(i) ==
    /\ i \in 1..N
    /\ creatures[i].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ mall' = i
    /\ UNCHANGED <<creatures, total>>

Enter == \E i \in 1..N : Enter(i)

\* ----------------------------------------------------------------------
\* When the limit has been reached, a creature trying to enter fades out
\* ----------------------------------------------------------------------
Fade(i) ==
    /\ i \in 1..N
    /\ creatures[i].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ creatures' = [creatures EXCEPT ![i].color = Faded]
    /\ UNCHANGED <<mall, total>>

Fade == \E i \in 1..N : Fade(i)

\* ----------------------------------------------------------------------
\* A meeting occurs between the waiting creature (mall) and an arriving one
\* ----------------------------------------------------------------------
Meet(i) ==
    /\ i \in 1..N
    /\ i # mall
    /\ mall # MeetingPlaceEmpty
    /\ creatures[i].color # Faded
    /\ creatures[mall].color # Faded
    /\ total < M
    /\ LET newc == Complement(creatures[i].color, creatures[mall].color) IN
          /\ creatures' = [creatures EXCEPT
                            ![i] = [color |-> newc,
                                    count |-> @.count + 1],
                            ![mall] = [color |-> newc,
                                       count |-> @.count + 1]]
          /\ total' = total + 1
          /\ mall' = MeetingPlaceEmpty

Meet == \E i \in 1..N : Meet(i)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ Enter
    \/ Fade
    \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<creatures, mall, total>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ creatures \in [1..N -> [color : Colors, count : Nat]]
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat

\* ----------------------------------------------------------------------
\* Sum of meetings invariant
\* ----------------------------------------------------------------------
SumCounts == Sum({creatures[i].count : i \in 1..N})

SumMet == total = M => SumCounts = 2 * M

====