---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Readers and writers contend for one shared resource. A bounded FIFO queue
\* of pending requests decides who goes next; the head request is honored
\* only when it does not conflict with the current reader/writer set. "Begin" is
\* guarded by "no writer currently active" and, for a write request, "no
\* readers currently active", so readers and writers are never both active.

Actors == 1..NumActors
Requests == {"read", "write"}
MaxPending == 2

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq([req: Requests, who: Actors])
  /\ Len(queue) <= MaxPending

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

SubmitRead(a) ==
  /\ [req |-> "read", who |-> a] \notin set(queue)
  /\ Len(queue) < MaxPending
  /\ queue' = Append(queue, [req |-> "read", who |-> a])
  /\ UNCHANGED <<readers, writers>>

SubmitWrite(a) ==
  /\ [req |-> "write", who |-> a] \notin set(queue)
  /\ Len(queue) < MaxPending
  /\ queue' = Append(queue, [req |-> "write", who |-> a])
  /\ UNCHANGED <<readers, writers>>

Begin ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET hd == Head(queue) IN
       /\ IF hd.req = "read"
            THEN readers' = readers \cup {hd.who} /\ writers' = writers
            ELSE /\ readers = {}
                 /\ writers' = writers \cup {hd.who}
                 /\ readers' = readers
       /\ queue' = Tail(queue)

Stop ==
  /\ readers' = {}
  /\ writers' = {}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : SubmitRead(a)
  \/ \E a \in Actors : SubmitWrite(a)
  \/ Begin
  \/ Stop

Spec == Init /\ [][Next]_vars
          /\ WF_vars(\E a \in Actors : SubmitRead(a))
          /\ WF_vars(\E a \in Actors : SubmitWrite(a))
          /\ WF_vars(Begin)
          /\ WF_vars(Stop)

\* Readers and writers are mutually exclusive by construction, and a single
\* writer is never exceeded.
Safety ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ Cardinality(writers) <= 1

\* Fairness of "Begin" (head request only honored when conflict-free, so no
\* request stays stuck forever) plus the weak fairness on "SubmitRead" and
\* "SubmitWrite" together give each actor a reading and a writing turn.
Liveness ==
  /\ \A a \in Actors : <>(a \in readers)
  /\ \A a \in Actors : <>(a \in writers)
  /\ \A a \in Actors : <>(a \notin readers)
  /\ \A a \in Actors : <>(a \notin writers)

====