---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* State: a creature maps to its color and how many meetings it has been in.
\* A single meeting place holds at most one waiting creature.
\* The global counter tracks how many meetings have occurred in total.
VARIABLES color, met, place, total

vars == <<color, met, place, total>>

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

TypeOK ==
  /\ color \in [Creatures -> Colors]
  /\ met \in [Creatures -> 0..M]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in 0..M

Init ==
  /\ \E c \in [Creatures -> Colors \ {{Faded}}]:
       color = c
  /\ met = [i \in Creatures |-> 0]
  /\ place = MeetingPlaceEmpty
  /\ total = 0

\* A creature enters the meeting place and waits for a partner.
Enter ==
  /\ place = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in Creatures:
       /\ color[i] # Faded
       /\ place' = i
  /\ UNCHANGED <<color, met, total>>

\* With the meeting place closed, an arriving creature simply fades.
FadeOut ==
  /\ place = MeetingPlaceEmpty
  /\ total >= M
  /\ \E i \in Creatures:
       /\ color[i] # Faded
       /\ color' = [color EXCEPT ![i] = Faded]
  /\ UNCHANGED <<met, place, total>>

\* Two different creatures meet; both adopt the complement of their colors.
MeetAndMutate ==
  /\ place # MeetingPlaceEmpty
  /\ \E i \in Creatures:
       /\ i # place
       /\ met[i] < M
       /\ met[place] < M
       /\ LET f == Complement(color[i], color[place])
          IN
            /\ color' = [color EXCEPT ![i] = f, ![place] = f]
            /\ met' = [met EXCEPT ![i] = @ + 1, ![place] = @ + 1]
            /\ total' = total + 1
            /\ place' = MeetingPlaceEmpty

Next == Enter \/ FadeOut \/ MeetAndMutate

Spec == Init /\ [][Next]_vars

SumMet ==
  \E s \in 0..(2 * M):
    /\ total = M => s = 2 * M
    /\ s = met[1] + met[2] + met[3]

\* Complement rule: same colors stay, different colors become the third.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in Colors \ {{Faded}} : c # c1 /\ c # c2

====