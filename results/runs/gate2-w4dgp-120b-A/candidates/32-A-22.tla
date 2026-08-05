---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0
ASSUME M \in Nat /\ M > 0
ASSUME Faded \notin (Nat .. 3)
ASSUME MeetingPlaceEmpty \notin (Nat .. 2)

Creatures == 0 .. (N - 1)

Colors == 0 .. 3

VARIABLES proband, met, totalMet

vars == <<proband, met, totalMet>>

Complement(c1, c2) == IF c1 = c2 THEN c1 ELSE (({0, 1, 2} \ {c1, c2}) \cup {3}) \ {3}

RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN met[x][2] + SumOver(S \ {x})

TypeOK ==
    /\ proband \in [Creatures -> [0 .. 3] \X (Nat .. M)]
    /\ totalMet \in 0 .. M
    /\ \E w \in Creatures \cup {MeetingPlaceEmpty} : \A e \in proband : e[1] \in {w} \cup Creatures

Init ==
    /\ proband = [e \in Creatures |-> <<CHOOSE c \in {0, 1, 2} : TRUE, 0>>]
    /\ totalMet = 0
    /\ \E w \in Creatures \cup {MeetingPlaceEmpty} : proband[w][1] = MeetingPlaceEmpty

EnterMeetingPlace(e) ==
    /\ proband[e][1] # Faded
    /\ totalMet < M
    /\ \A f \in Creatures : proband[f][1] # MeetingPlaceEmpty
    /\ proband' = [proband EXCEPT ![e][1] = MeetingPlaceEmpty]
    /\ UNCHANGED totalMet

FadeOut(e) ==
    /\ proband[e][1] # Faded
    /\ totalMet >= M
    /\ proband[e][1] # MeetingPlaceEmpty
    /\ proband' = [proband EXCEPT ![e][1] = Faded]
    /\ UNCHANGED totalMet

Meet(e) ==
    /\ proband[e][1] # Faded
    /\ \E w \in Creatures :
        /\ proband[w][1] = MeetingPlaceEmpty
        /\ e # w
        /\ proband[e][2] < M
        /\ proband[w][2] < M
        /\ proband' = [proband EXCEPT ![e] = <<Complement(proband[e][1], proband[w][1]), proband[e][2] + 1>>,
                                ![w] = <<Complement(proband[e][1], proband[w][1]), proband[w][2] + 1>>]
    /\ totalMet' = totalMet + 1

Next ==
    \/ \E e \in Creatures : EnterMeetingPlace(e)
    \/ \E e \in Creatures : FadeOut(e)
    \/ \E e \in Creatures : Meet(e)

Spec == Init /\ [][Next]_vars

SumMet == (totalMet = M => SumOver(Creatures) = 2 * M)

====