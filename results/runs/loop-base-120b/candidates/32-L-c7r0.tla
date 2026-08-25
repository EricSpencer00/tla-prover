---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(***************************************************************************)
(*  Definitions of basic sets                                            *)
(***************************************************************************)

Colors == {"blue", "red", "yellow"}

Creature == 1..N

(***************************************************************************)
(*  State variables                                                      *)
(***************************************************************************)

VARIABLES cre, mall, total

(***************************************************************************)
(*  Helper definitions                                                   *)
(***************************************************************************)

NonFaded(i) == cre[i].color \in Colors

Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in Colors : c # c1 /\ c # c2

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)

Init ==
    /\ cre \in [Creature -> [color : Colors, count : Nat]]
    /\ \A i \in Creature: cre[i].count = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in Creature :
        /\ NonFaded(i)
        /\ mall' = i
        /\ cre' = cre
        /\ total' = total

Fade ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E i \in Creature :
        /\ NonFaded(i)
        /\ cre' = [cre EXCEPT ![i].color = Faded]
        /\ mall' = MeetingPlaceEmpty
        /\ total' = total

Meet ==
    /\ mall \in Creature
    /\ total < M
    /\ \E i \in Creature :
        /\ i # mall
        /\ NonFaded(i) /\ NonFaded(mall)
        LET newCol == Complement(cre[i].color, cre[mall].color) IN
          /\ cre' = [cre EXCEPT
                        ![i].color = newCol,
                        ![i].count = @ + 1,
                        ![mall].color = newCol,
                        ![mall].count = @ + 1]
          /\ mall' = MeetingPlaceEmpty
          /\ total' = total + 1

Next == Enter \/ Fade \/ Meet

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<cre, mall, total>>

(***************************************************************************)
(*  Invariants                                                            *)
(***************************************************************************)

TypeOK ==
    /\ cre \in [Creature -> [color : (Colors \cup {Faded}), count : Nat]]
    /\ mall \in (Creature \cup {MeetingPlaceEmpty})
    /\ total \in Nat

SumMet ==
    total = M => Sum(i \in Creature: cre[i].count) = 2 * M

=============================================================================