-------------------------- MODULE W4Od0m0p6t3 --------------------------
EXTENDS Integers

CONSTANTS Surgeons, Rooms, MaxIssue, Vacant

NoRead == [rm |-> Vacant, ce |-> -1]
Reads  == {NoRead} \cup [rm : Rooms, ce : 0 .. MaxIssue]

VARIABLES issue, booked, stamp, jotting, operated
vars == <<issue, booked, stamp, jotting, operated>>

\* Nobody latches a room. A surgeon reads a room as free together with the
\* issue number of the badge it is holding, then comes back and books, which
\* is refused unless the room is still free and the badge has not been
\* re-issued underneath it. A surgeon here is slow, never absent.
\* Each standing booking is stamped with the badge issue that was presented.
TypeOK ==
  /\ issue \in [Surgeons -> 0 .. MaxIssue]
  /\ booked \in [Rooms -> Surgeons \cup {Vacant}]
  /\ stamp \in [Rooms -> 0 .. MaxIssue]
  /\ jotting \in [Surgeons -> Reads]
  /\ operated \subseteq Surgeons

Init ==
  /\ issue = [g \in Surgeons |-> 0]
  /\ booked = [k \in Rooms |-> Vacant]
  /\ stamp = [k \in Rooms |-> 0]
  /\ jotting = [g \in Surgeons |-> NoRead]
  /\ operated = {}

Study(g, k) ==
  /\ g \notin operated
  /\ jotting[g] = NoRead
  /\ booked[k] = Vacant
  /\ jotting' = [jotting EXCEPT ![g] = [rm |-> k, ce |-> issue[g]]]
  /\ UNCHANGED <<issue, booked, stamp, operated>>

Book(g) ==
  /\ jotting[g] # NoRead
  /\ booked[jotting[g].rm] = Vacant
  /\ issue[g] = jotting[g].ce
  /\ booked' = [booked EXCEPT ![jotting[g].rm] = g]
  /\ stamp' = [stamp EXCEPT ![jotting[g].rm] = jotting[g].ce]
  /\ jotting' = [jotting EXCEPT ![g] = NoRead]
  /\ UNCHANGED <<issue, operated>>

Retry(g) ==
  /\ jotting[g] # NoRead
  /\ \/ booked[jotting[g].rm] # Vacant
     \/ issue[g] # jotting[g].ce
  /\ jotting' = [jotting EXCEPT ![g] = NoRead]
  /\ UNCHANGED <<issue, booked, stamp, operated>>

Operate(g, k) ==
  /\ booked[k] = g
  /\ stamp[k] = issue[g]
  /\ booked' = [booked EXCEPT ![k] = Vacant]
  /\ operated' = operated \cup {g}
  /\ UNCHANGED <<issue, stamp, jotting>>

\* Re-issuing a badge must also strike every booking that badge is holding,
\* otherwise a room would be standing reserved to an authority nobody holds.
Reissue(g) ==
  /\ issue[g] < MaxIssue
  /\ issue' = [issue EXCEPT ![g] = @ + 1]
  /\ booked' = [k \in Rooms |-> IF booked[k] = g THEN Vacant ELSE booked[k]]
  /\ UNCHANGED <<stamp, jotting, operated>>

StudyStep   == \E g \in Surgeons, k \in Rooms : Study(g, k)
BookStep    == \E g \in Surgeons : Book(g)
RetryStep   == \E g \in Surgeons : Retry(g)
OperateStep == \E g \in Surgeons, k \in Rooms : Operate(g, k)

Next == StudyStep \/ BookStep \/ RetryStep \/ OperateStep
        \/ \E g \in Surgeons : Reissue(g)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StudyStep) /\ WF_vars(BookStep)
        /\ WF_vars(RetryStep) /\ WF_vars(OperateStep)

\* No stale authority: every room standing booked is stamped with exactly the
\* badge issue its holder is carrying now, so no booking rests on a badge that
\* has since been re-issued.
NoStaleBooking ==
  \A k \in Rooms : booked[k] # Vacant => stamp[k] = issue[booked[k]]

EveryoneOperates == <>(\A g \in Surgeons : g \in operated)
========================================================================