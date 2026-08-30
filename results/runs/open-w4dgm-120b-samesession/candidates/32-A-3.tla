---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow"}
ColorCount == 3

\* Mutual complement of two colors: the third one in the cycle, or unchanged if equal.
Complement(x, y) == IF x = y THEN x ELSE CASE x = "blue" /\ y = "red" -> "yellow"
                                          [] x = "red" /\ y = "blue" -> "yellow"
                                          [] x = "blue" /\ y = "yellow" -> "red"
                                          [] x = "yellow" /\ y = "blue" -> "red"
                                          [] x = "red" /\ y = "yellow" -> "blue"
                                          [] x = "yellow" /\ y = "red" -> "blue"
                                          [] OTHER -> x

RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN Cre[x][2] + SumOver(S \ {x})

VARIABLES Cre, MeetingPlace, TotalMet

vars == << Cre, MeetingPlace, TotalMet >>

TypeOK ==
    /\ Cre \in [Creatures -> (Colors \cup {Faded}) \X (0..M)]
    /\ MeetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ TotalMet \in 0..M

Init ==
    /\ \E initCol \in [Creatures -> Colors] :
         Cre = [c \in Creatures |-> << initCol[c], 0 >>]
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMet = 0

EnterPlace(c) ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMet < M
    /\ Cre[c][1] # Faded
    /\ MeetingPlace' = c
    /\ UNCHANGED << Cre, TotalMet >>

FadeOut(c) ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMet = M
    /\ Cre[c][1] # Faded
    /\ Cre' = [Cre EXCEPT ![c][1] = Faded]
    /\ UNCHANGED << MeetingPlace, TotalMet >>

Meet(m) ==
    /\ MeetingPlace # MeetingPlaceEmpty
    /\ MeetingPlace # m
    /\ Cre[m][1] # Faded
    /\ Cre[MeetingPlace][1] # Faded
    /\ TotalMet < M
    /\ Cre' = [Cre EXCEPT ![m] = << Complement(Cre[m][1], Cre[MeetingPlace][1]), Cre[m][2] + 1 >>,
               ![MeetingPlace] = << Complement(Cre[MeetingPlace][1], Cre[m][1]), Cre[MeetingPlace][2] + 1 >>]
    /\ TotalMet' = TotalMet + 1
    /\ MeetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterPlace(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E m \in Creatures : Meet(m)

Spec == Init /\ [][Next]_vars

\* Every meeting is a two-way encounter, so the summed per-creature counts
\* double the met count once meeting capacity is exhausted.
SumMet == SumOver(Creatures)

MaxMetZero == IF M = 0 THEN 1 ELSE M
\* Typesafe division: the bound is at least one, so the denominator is never zero.
SumMetInSync ==
    /\ TotalMet = MaxMetZero
    /\ SumMet = 2 * TotalMet

TypeOKInv == TypeOK
SumMetInv == SumMetInSync

====