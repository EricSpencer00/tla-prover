---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 1..NumActors

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq([proc : Actors, mode : {"read", "write"}])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

REQUEST_READ(e) ==
  /\ \A i \in 1..Len(queue) : queue[i].proc # e
  /\ queue' = Append(queue, [proc |-> e, mode |-> "read"])
  /\ UNCHANGED <<reading, writing>>

REQUEST_WRITE(e) ==
  /\ \A i \in 1..Len(queue) : queue[i].proc # e
  /\ queue' = Append(queue, [proc |-> e, mode |-> "write"])
  /\ UNCHANGED <<reading, writing>>

BEGIN_RW ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET q == Head(queue) IN
       /\ IF q.mode = "write"
            THEN /\ reading = {} /\ writing' = {q.proc}
            ELSE /\ reading' = reading \cup {q.proc}
                 /\ UNCHANGED writing
       /\ queue' = Tail(queue)

STOP_ACTIVITY(e) ==
  /\ (e \in reading \/ e \in writing)
  /\ reading' = reading \ {e}
  /\ writing' = writing \ {e}
  /\ UNCHANGED queue

Next ==
  \/ \E e \in Actors : REQUEST_READ(e)
  \/ \E e \in Actors : REQUEST_WRITE(e)
  \/ BEGIN_RW
  \/ \E e \in Actors : STOP_ACTIVITY(e)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E e \in Actors : REQUEST_READ(e))
  /\ WF_vars(\E e \in Actors : REQUEST_WRITE(e))
  /\ WF_vars(BEGIN_RW)
  /\ WF_vars(\E e \in Actors : STOP_ACTIVITY(e))

Safety ==
  /\ writing # {} => reading = {}
  /\ \A a, b \in writing : a = b
  /\ \A p \in Actors : (p \in reading \/ p \in writing) => (p \notin reading \/ p \notin writing)

Liveness ==
  /\ \A e \in Actors : (e \in reading) ~> (e \notin reading)
  /\ \A e \in Actors : (e \in writing) ~> (e \notin writing)
  /\ \A e \in Actors : TRUE ~> (e \in reading)
  /\ \A e \in Actors : TRUE ~> (e \in writing)

n == 3
====