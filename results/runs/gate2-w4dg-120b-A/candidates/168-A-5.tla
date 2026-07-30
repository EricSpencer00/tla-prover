---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 1 .. NumActors
Modes == {"read", "write"}

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Req == [mode: Modes, proc: Actors]

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in Seq(Req)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ \A k \in 1 .. Len(queue) : queue[k].proc # a
    /\ queue' = Append(queue, [mode |-> "read", proc |-> a])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
    /\ \A k \in 1 .. Len(queue) : queue[k].proc # a
    /\ queue' = Append(queue, [mode |-> "write", proc |-> a])
    /\ UNCHANGED <<readers, writers>>

\* Readers are admitted freely; writers wait for exclusive access.
ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET front == Head(queue)
           remQueue == Tail(queue)
       IN IF front.mode = "read" THEN
              /\ readers' = readers \cup {front.proc}
              /\ queue' = remQueue
          ELSE
              /\ readers = {}
              /\ writers' = writers \cup {front.proc}
              /\ queue' = remQueue
    /\ UNCHANGED writers

StopActivity(a) ==
    /\ \/ a \in readers
       /\ readers' = readers \ {a}
    \/ \/ a \in writers
       /\ writers' = writers \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ ProcessQueue
    \/ \E a \in Actors : StopActivity(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ProcessQueue)
    /\ \A a \in Actors : WF_vars(RequestRead(a))
    /\ \A a \in Actors : WF_vars(RequestWrite(a))
    /\ \A a \in Actors : WF_vars(StopActivity(a))

Safety ==
    /\ (writers # {} => readers = {})
    /\ (readers # {} => writers = {})
    /\ Cardinality(writers) <= 1

Liveness ==
    \A a \in Actors :
        /\ (\A S \in {readers, writers} : (a \in S) ~> (a \notin S))
        /\ (\A S \in {readers, writers} : (a \notin S) ~> (a \in S))

====