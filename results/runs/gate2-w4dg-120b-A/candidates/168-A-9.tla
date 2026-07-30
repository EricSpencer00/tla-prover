---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1 .. NumActors

VARIABLES readers, writers, reqQueue

vars == <<readers, writers, reqQueue>>

Req == [process: Actors, mode: {"read", "write"}]

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ reqQueue \in Seq(Req)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ reqQueue = <<>>

RequestRead(a) ==
  /\ \A i \in 1 .. Len(reqQueue) : reqQueue[i].process # a
  /\ reqQueue' = Append(reqQueue, [process |-> a, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ \A i \in 1 .. Len(reqQueue) : reqQueue[i].process # a
  /\ reqQueue' = Append(reqQueue, [process |-> a, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

BeginReadWrite ==
  /\ reqQueue # <<>>
  /\ writers = {}
  /\ LET h == Head(reqQueue) IN
       IF h.mode = "read" THEN
         readers' = readers \cup {h.process}
       ELSE IF readers = {} THEN
         writers' = writers \cup {h.process}
       ELSE
         UNCHANGED <<readers, writers>>
     /\ reqQueue' = Tail(reqQueue)

StopActivity(a) ==
  /\ (a \in readers \/ a \in writers)
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ UNCHANGED reqQueue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ BeginReadWrite
  \/ \E a \in Actors : StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors : RequestRead(a))
  /\ WF_vars(\E a \in Actors : RequestWrite(a))
  /\ WF_vars(BeginReadWrite)
  /\ WF_vars(\E a \in Actors : StopActivity(a))

Safety ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ \A a, b \in Actors : (a \in writers /\ b \in writers) => a = b

Liveness ==
  \A a \in Actors :
    /\ (a \in readers) ~> (a \notin readers)
    /\ (a \in writers) ~> (a \notin writers)

====