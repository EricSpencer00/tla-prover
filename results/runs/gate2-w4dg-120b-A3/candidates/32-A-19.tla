---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* CreatureState is a pair: [color : {blue, red, yellow, Faded}, meetings : 0..M]
Creatures == 1..N
Colors == {"blue", "red", "yellow"}
InitialColors == Colors

\* M(i) = i's color; P(i) = i's meeting count
CreatureState == [color : Colors \cup {Faded}, meetings : 0..M]

VARIABLES creature, mall, totalMeetings
vars == <<creature, mall, totalMeetings>>

RECURSIVE SumF(_, _)
SumF(f, S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumF(f, S \ {x})

TypeOK ==
  /\ creature \in [Creatures -> CreatureState]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ creature \in [Creatures -> [color : InitialColors, meetings : 0]]
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* The complement rule: same colors stay, different colors become the third one.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET r == {"blue", "red", "yellow"} \ {c1, c2} IN CHOOSE x \in r : TRUE

Enter(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ creature[i].color # Faded
  /\ totalMeetings < M
  /\ mall' = i
  /\ UNCHANGED <<creature, totalMeetings>>

FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ \E i \in Creatures :
       /\ creature[i].color # Faded
       /\ creature' = [creature EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<mall, totalMeetings>>

\* Two participants: the entering creature and the one waiting in the mall.
Meet(i) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # i
  /\ totalMeetings < M
  /\ LET cnew == Complement(creature[i].color, creature[mall].color) IN
       creature' = [creature EXCEPT ![i].color = cnew, ![i].meetings = @ + 1,
                                    ![mall].color = cnew, ![mall].meetings = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ mall' = MeetingPlaceEmpty

Next == (\E i \in Creatures : Enter(i)) \/ FadeOut \/ (\E i \in Creatures : Meet(i))

Spec == Init /\ [][Next]_vars

\* Every meeting involves two participants, so when the counter is exhausted
\* the individual counts add up to exactly twice the number of meetings.
SumMet == totalMeetings = M => SumF([i \in Creatures |-> creature[i].meetings], Creatures) = 2 * M

====