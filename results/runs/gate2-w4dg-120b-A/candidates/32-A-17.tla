---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* N: number of chameneos; M: meeting limit; Faded: fade marker; MeetingPlaceEmpty: empty place.

Colors == {"blue", "red", "yellow"}
Creatures == 1..N
Complement(c1, c2) == IF c1 = c2 THEN c1 ELSE CHOOSE c \in Colors :
                                          \A c' \in {c1, c2} : c' # c

VARIABLES cham, mall, meetings
vars == <<cham, mall, meetings>>

RECURSIVE SumOf(_)
SumOf(S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE e \in S : TRUE
                 IN cham[x][2] + SumOf(S \ {x})

TypeOK ==
    /\ cham \in [Creatures -> (Colors \cup {Faded}) \X (0..M)]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ meetings \in 0..M

Init ==
    /\ cham = [c \in Creatures |-> <<CHOOSE cl \in Colors : TRUE, 0>>]
    /\ mall = MeetingPlaceEmpty
    /\ meetings = 0

Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ meetings < M
    /\ cham[c][1] # Faded
    /\ mall' = c
    /\ UNCHANGED <<cham, meetings>>

Fade(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ meetings = M
    /\ cham[c][1] # Faded
    /\ cham' = [cham EXCEPT ![c][1] = Faded]
    /\ UNCHANGED <<mall, meetings>>

Meet(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ cham[c][1] # Faded
    /\ cham[mall][1] # Faded
    /\ cham' = [cham EXCEPT ![c] = <<Complement(cham[c][1], cham[mall][1]), @ [2] + 1>>,
                            ![mall] = <<Complement(cham[c][1], cham[mall][1]), @ [2] + 1>>]
    /\ meetings' = meetings + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : Fade(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet == (meetings = M) => (SumOf(Creatures) = 2 * M)
====