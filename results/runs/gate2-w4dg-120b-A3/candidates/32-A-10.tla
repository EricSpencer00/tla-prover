---- MODULE Chameneos ----
EXTENDS Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 0 .. (N - 1)

Colors == {"blue", "red", "yellow", Faded}

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET S == {c1, c2} IN CHOOSE x \in Colors \ {c1, c2, Faded} : TRUE

SumCounts ==
    LET f[Z \in SUBSET Creatures] ==
        IF Z = {} THEN 0
        ELSE LET x == CHOOSE y \in Z : TRUE IN x[2] + f[Z \ {x}]
    IN f[Creatures]

VARIABLES status, waiting, meetings

vars == <<status, waiting, meetings>>

TypeOK ==
    /\ status \in [Creatures -> (Colors \X 0..M)]
    /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
    /\ meetings \in 0..M

Init ==
    /\ status \in [Creatures -> ({"blue", "red", "yellow"} \X {0})]
    /\ waiting = MeetingPlaceEmpty
    /\ meetings = 0

FadeOut(c) ==
    /\ status[c][1] # Faded
    /\ status' = [status EXCEPT ![c] = <<Faded, status[c][2]>>]
    /\ UNCHANGED <<waiting, meetings>>

EnterPlace(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ status[c][1] # Faded
    /\ meetings < M
    /\ waiting' = c
    /\ UNCHANGED <<status, meetings>>

MeetAndMutate(c) ==
    /\ waiting # MeetingPlaceEmpty
    /\ waiting # c
    /\ status[c][1] # Faded
    /\ status[waiting][1] # Faded
    /\ LET nc == Complement(status[c][1], status[waiting][1]) IN
        status' = [status EXCEPT ![c] = <<nc, status[c][2] + 1>>, ![waiting] = <<nc, status[waiting][2] + 1>>]
    /\ meetings' = meetings + 1
    /\ waiting' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)
    \/ \E c \in Creatures : EnterPlace(c)

Spec == Init /\ [][Next]_vars

SumMet == meetings = M => SumCounts = 2 * M

====