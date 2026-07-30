---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N

VARIABLES pc, meetingPlace, globalCount
vars == <<pc, meetingPlace, globalCount>>

Colors == {"blue", "red", "yellow", Faded}

\* Complement rule: same color stays the same; different colors both become
\* the third color not currently held by either creature.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET s == {c1, c2} IN (CHOOSE c \in Colors : c \notin s)

TotalMeetings == LET g[S \in SUBSET Creatures] ==
                     IF S = {} THEN 0
                     ELSE LET x == CHOOSE e \in S : TRUE
                          IN pc[x][2] + g[S \ {x}]
                 IN g[Creatures]

\* The per-creature meeting counts must sum to twice the total meetings
\* because every meeting involves exactly two participants.
SumCounts == LET g[S \in SUBSET Creatures] ==
                 IF S = {} THEN 0
                 ELSE LET x == CHOOSE e \in S : TRUE
                      IN pc[x][2] + g[S \ {x}]
             IN g[Creatures]

Init ==
  /\ pc = [c \in Creatures |-> <<CHOOSE col \in Colors \ {Faded} : TRUE, 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ globalCount = 0

Enter ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ globalCount < M
  /\ \E c \in Creatures :
       /\ pc[c][1] # Faded
       /\ meetingPlace' = c
  /\ UNCHANGED <<pc, globalCount>>

FadeOut ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ globalCount >= M
  /\ \E c \in Creatures :
       /\ pc[c][1] # Faded
       /\ pc' = [pc EXCEPT ![c][1] = Faded]
  /\ UNCHANGED <<meetingPlace, globalCount>>

MeetAndMutate ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # globalCount
  /\ pc[meetingPlace][1] # Faded
  /\ \E c \in Creatures :
       /\ c # meetingPlace
       /\ pc[c][1] # Faded
       /\ LET newcol == Complement(pc[meetingPlace][1], pc[c][1]) IN
            /\ pc' = [pc EXCEPT ![meetingPlace][1] = newcol, ![c][1] = newcol,
                                   ![meetingPlace][2] = pc[meetingPlace][2] + 1,
                                   ![c][2] = pc[c][2] + 1]
       /\ globalCount' = globalCount + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next == Enter \/ FadeOut \/ MeetAndMutate

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ pc \in [Creatures -> (Colors \X (0 .. M))]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ globalCount \in 0 .. M

MeetingCountConservation ==
  globalCount = M => SumCounts = 2 * M

====