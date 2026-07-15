---- MODULE Chameneos ----
EXTENDS Integers

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLE chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

(* Type correctness *)
TypeOK ==
   /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in Nat

(* Initial predicate *)
Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

(* Single-step transition for a chameneos with identifier cid *)
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty THEN
      IF numMeetings < N THEN
         /\ meetingPlace' = cid
         /\ UNCHANGED <<chameneoses, numMeetings>>
      ELSE
         /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
         /\ UNCHANGED <<meetingPlace, numMeetings>>
   ELSE
      /\ meetingPlace /= cid
      /\ meetingPlace' = MeetingPlaceEmpty
      /\ numMeetings' = numMeetings + 1
      /\ chameneoses' =
          LET newColor == Complement(chameneoses[cid][1],
                                    chameneoses[meetingPlace][1])
          IN [chameneoses EXCEPT
                ![cid] = <<newColor, @[2] + 1>>,
                ![meetingPlace] = <<newColor, @[2] + 1>>]

(* Non-deterministic choice of a non‑faded chameneos to try to enter the meeting place *)
Next ==
   /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
   /\ UNCHANGED vars \ {meetingPlace, numMeetings, chameneoses}

Spec == Init /\ [][Next]_vars

(* Invariant relating the total number of individual meetings to the global counter *)
SumMet == numMeetings = N => LET f[c \in ChameneosID] == chameneoses[c][2]
                               IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====