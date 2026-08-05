---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent and          *)
(* symmetrical cooperation - the game described in the Chameneos paper      *)
(* (https://cedric.cnam.fr/fichiers/RC474.pdf).  The game runs until all   *)
(* chameneoses have taken on the faded color.                             *)
(*                                                                         *)
(* An agent (a chameneos creature) enters an empty meeting place (the        *)
(* mall), where it waits to meet another agent.  When it meets another       *)
(* agent, both agents emerge from the meeting place with a new color that    *)
(* depends on the two colors that entered, and each marks that it has        *)
(* participated in one more meeting.  An agent that tries to enter the       *)
(* meeting place once the maximum number of meetings has already taken       *)
(* place is faded and stops participating.                                 *)
(*                                                                         *)
(* THIS SPEC REQUIRES EXACTLY ONE change from the version that fails TLC:  *)
(* an action must always explicitly assign every variable in the model,      *)
(* because a successor state that leaves a variable unassigned is reported    *)
(* by TLC as an error rather than as a modeling mistake.  The change adds    *)
(* an explicit 'UNCHANGED' clause to the branch that marks an agent faded,   *)
(* so the meetingPlace and numMeetings variables are never left unspecified. *)
(*                                                                         *)
(* That change is purely syntactic - the semantics of the game, the          *)
(* termination property, and the meaning of all other clauses are untouched. *)
(***************************************************************************)
EXTENDS Integers

RecurS(f, S) == IF S = {} THEN 0
                     ELSE LET x == CHOOSE x \in S : TRUE
                          IN  f[x] + RecurS(f, S \ {x})

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* N = number of meetings after which chameneoses fade; M = number of creatures
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesId == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesId

TypeOK ==
   /\ chameneoses \in [ChameneosesId -> (Color \cup {Faded}) \X (0 .. N)]
   /\ meetingPlace \in ChameneosesId \cup {MeetingPlaceEmpty}

Init ==
   /\ chameneoses \in [ChameneosesId -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* An agent enters the meeting place (or, once the limit is reached, fades)
\* or two agents in the meeting place mutate into a new color together.
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty
   THEN IF numMeetings < N
        THEN /\ meetingPlace' = cid
             /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
             /\ UNCHANGED <<meetingPlace, numMeetings>>
   ELSE /\ meetingPlace # cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ numMeetings' = numMeetings + 1
        /\ chameneoses' =
             LET newColor == Complement(chameneoses[cid][1],
                                        chameneoses[meetingPlace][1])
             IN [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                        ![meetingPlace] = <<newColor, @[2] + 1>>]

\* Any non-faded agent may try to enter the meeting place
Next == \E c \in { x \in ChameneosesId : chameneoses[x][1] # Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

\* When the game terminates, the total number of meetings attended by all
\* agents equals 2*N: every meeting is shared by exactly two agents, so its
\* attendance is counted twice in the sum.
SumMet ==
   numMeetings = N =>
     LET f[c \in ChameneosesId] == chameneoses[c][2]
     IN RecurS(f, ChameneosesId) = 2 * N
THEOREM Spec => []SumMet

====