---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a tuple <<color, met>>, where met counts that creature's
\* individual meetings and the global counter tracks system-wide meetings.
Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES phase, mall, total

vars == <<phase, mall, total>>

TypeOK ==
    /\ phase \in [Creatures -> [color: Colors, met: 0 .. M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in 0 .. M

Init ==
    /\ phase = [c \in Creatures |-> [color |-> "blue", met |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* Enter the empty meeting place while meetings remain.
Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ phase[c].color # Faded
    /\ mall' = c
    /\ UNCHANGED <<phase, total>>

\* When closed, a non-faded creature that tries to enter fades out.
Fade(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ phase[c].color # Faded
    /\ phase' = [phase EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, total>>

\* Two distinct creatures meet and both adopt the same complement color.
\* This is the only action that advances the global meeting counter.
Meet(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ phase[c].color # Faded
    /\ phase[mall].color # Faded
    /\ total < M
    /\ LET
        newcol == IF phase[c].color = phase[mall].color
                    THEN phase[c].color
                    ELSE CHOOSE e \in {"blue", "red", "yellow"} :
                            e # phase[c].color /\ e # phase[mall].color
       IN
        phase' = [phase EXCEPT ![c] = [color |-> newcol, met |-> @.met + 1],
                              ![mall] = [color |-> newcol, met |-> @.met + 1]]
    /\ total' = total + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : Fade(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* At the meeting limit, the per-creature meeting total equals twice the
\* global meeting count -- each meeting touched two participants exactly.
SumMet ==
    /\ total = M
    /\ (2 * total) = (phase[1].met + phase[2].met + phase[3].met)

\* Every creature eventually fades out and the meeting place stays empty.
AllFaded == <>(mall = MeetingPlaceEmpty /\ \A c \in Creatures : phase[c].color = Faded)

====