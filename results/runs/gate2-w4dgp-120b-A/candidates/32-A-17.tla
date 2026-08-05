---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Chameneos creatures meet pairwise at a central place (the Mall); each meeting
\* changes both participants' colors by a complementation rule. A global meeting
\* counter caps how many meetings occur; once it reaches M the meeting place
\* closes and creatures that try to enter there instead fade. The invariant
\* checks that every meeting is accounted for twice in the per-creature counts.
CREATURES == 1 .. N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES status, mall, metCount
vars == <<status, mall, metCount>>

\* Complement: same color stays, otherwise both adopt the third color.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE (CHOOSE c3 \in {"blue", "red", "yellow"} : c3 # c1 /\ c3 # c2)

TypeOK ==
  /\ status \in [CREATURES -> [color : Colors, met : 0 .. M]]
  /\ mall \in CREATURES \cup {MeetingPlaceEmpty}
  /\ metCount \in 0 .. M

Init ==
  /\ status = [c \in CREATURES |-> [color |-> CHOOSE c0 \in {"blue", "red", "yellow"} : TRUE,
                                    met |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ metCount = 0

\* A creature enters the empty meeting place to wait for a partner.
Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ metCount < M
  /\ status[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED <<status, metCount>>

\* Once the cap is reached and the place is empty, an arriving creature fades out.
Fade(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ metCount = M
  /\ status[c].color # Faded
  /\ status' = [status EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, metCount>>

\* Two different creatures meet and both adopt the complement of their colors.
Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ metCount' = metCount + 1
  /\ status' = [status EXCEPT ![c].color = Complement(status[c].color, status[mall].color),
                           ![c].met = status[c].met + 1,
                           ![mall].color = Complement(status[c].color, status[mall].color),
                           ![mall].met = status[mall].met + 1]
  /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E c \in CREATURES : Enter(c)
  \/ \E c \in CREATURES : Fade(c)
  \/ \E c \in CREATURES : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet == metCount = M => (metCount * 2) = (status[1].met + status[2].met + status[3].met)

====