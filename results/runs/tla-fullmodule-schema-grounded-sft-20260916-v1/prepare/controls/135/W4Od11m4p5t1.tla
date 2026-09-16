---- MODULE W4Od11m4p5t1 ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Jobs, Reqs, MaxQ, MaxInbox

VARIABLES inbox, queue, printLog, busy

vars == <<inbox, queue, printLog, busy>>
Ran(s) == {s[i] : i \in DOMAIN s}

TypeOK ==
  /\ inbox \subseteq [job: Jobs, rid: Reqs]
  /\ queue \in Seq(Jobs)
  /\ printLog \in Seq(Jobs)
  /\ busy \in BOOLEAN

Init ==
  /\ inbox = {}
  /\ queue = << >>
  /\ printLog = << >>
  /\ busy = FALSE

Submit(j, r) ==
  /\ Cardinality(inbox) < MaxInbox
  /\ [job |-> j, rid |-> r] \notin inbox
  /\ inbox' = inbox \cup {[job |-> j, rid |-> r]}
  /\ UNCHANGED <<queue, printLog, busy>>

Enqueue(m) ==
  /\ m \in inbox
  /\ Len(queue) < MaxQ
  /\ m.job \notin Ran(queue)
  /\ queue' = Append(queue, m.job)
  /\ inbox' = inbox \ {m}
  /\ UNCHANGED <<printLog, busy>>

Print ==
  /\ queue # << >>
  /\ ~busy
  /\ Head(queue) \notin Ran(printLog)
  /\ printLog' = Append(printLog, Head(queue))
  /\ queue' = Tail(queue)
  /\ busy' = TRUE
  /\ UNCHANGED <<inbox>>

Discard ==
  /\ queue # << >>
  /\ Head(queue) \in Ran(printLog)
  /\ queue' = Tail(queue)
  /\ UNCHANGED <<inbox, printLog, busy>>

Complete ==
  /\ busy
  /\ busy' = FALSE
  /\ UNCHANGED <<inbox, queue, printLog>>

Next ==
  \/ \E j \in Jobs, r \in Reqs: Submit(j, r)
  \/ \E m \in inbox: Enqueue(m)
  \/ Print
  \/ Discard
  \/ Complete

Spec == Init /\ [][Next]_vars

PrintAtMostOnce == Cardinality(Ran(printLog)) = Len(printLog)
====