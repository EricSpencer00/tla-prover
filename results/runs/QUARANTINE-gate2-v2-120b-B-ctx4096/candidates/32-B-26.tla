---- MODULE Chameneos ----
EXTENDS Integers

\* Recursive sum operator over a finite set
RECURSIVE Sum(_, _)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

\* Colors used by the chameneoses
Color == {"blue", "red", "yellow"}
\* A distinguished value that is not a color, used to indicate a faded chameneos
Faded == CHOOSE c : c \notin Color

\* Complement of two different colors (the third one)
Complement(c1, c2) == 
    IF c1 = c2 THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings
vars == <<chameneoses, meetingPlace, numMeetings>>

\* Identifiers of the chameneoses
ChameneosesID == 1 .. M
\* A value that is guaranteed not to be a chameneos identifier, used for an empty place
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* Type correctness (kept unchanged)
TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}

\* Initialization (kept unchanged)
Init ==
   /\ chameneoses \in [ChameneosesID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* One step of the protocol.
\* The action now explicitly assigns every variable in all branches,
\* ensuring that TLC sees the next-state relation as total.
Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty THEN
        IF numMeetings < N THEN
            /\ meetingPlace' = cid
            /\ chameneoses' = chameneoses
            /\ numMeetings' = numMeetings
        ELSE
            /\ meetingPlace' = meetingPlace
            /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
            /\ numMeetings' = numMeetings
    ELSE
        /\ meetingPlace /= cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
           IN chameneoses' =
                [chameneoses EXCEPT 
                   ![cid] = <<newColor, @[2] + 1>>,
                   ![meetingPlace] = <<newColor, @[2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* Choose a non‑faded chameneos to act
Next ==
    /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

\* Safety property from the paper
SumMet ==
    /\ numMeetings = N
    /\ LET f[c \in ChameneosesID] == chameneoses[c][2]
       IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====