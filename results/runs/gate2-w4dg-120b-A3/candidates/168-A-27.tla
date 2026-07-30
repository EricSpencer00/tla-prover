---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Process == 1 .. NumActors
ReqType == {"read", "write"}

QueueEntry == [actor: Process, kind: ReqType]

TypeOK ==
  /\ readers \subseteq Process
  /\ writers \subseteq Process
  /\ queue \in Seq(QueueEntry)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

\* A process appends a read request to the end of the waiting queue.
RequestRead(p) ==
  /\ \A k \in 1 .. Len(queue): queue[k].actor # p
  /\ queue' = Append(queue, [actor |-> p, kind |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* A process appends a write request to the end of the waiting queue.
RequestWrite(p) ==
  /\ \A k \in 1 .. Len(queue): queue[k].actor # p
  /\ queue' = Append(queue, [actor |-> p, kind |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* The head of the queue begins its access only if it is compatible with the
\* current activity, and it is then removed from the queue.
Begin ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET h == Head(queue) IN
       /\ IF h.kind = "read"
            THEN readers' = readers \cup {h.actor} /\ writers' = writers
            ELSE /\ writers' = writers \cup {h.actor} /\ readers' = {}
       /\ queue' = Tail(queue)

\* An active reader or writer voluntarily stops.
Stop ==
  /\ readers # {}
  /\ \E p \in readers: readers' = readers \ {p} /\ UNCHANGED <<writers, queue>>
  \/ writers # {}
  /\ \E p \in writers: writers' = writers \ {p} /\ UNCHANGED <<readers, queue>>

Next ==
  \/ \E p \in Process: RequestRead(p)
  \/ \E p \in Process: RequestWrite(p)
  \/ Begin
  \/ Stop

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Process: RequestRead(p))
  /\ WF_vars(\E p \in Process: RequestWrite(p))
  /\ WF_vars(Begin)
  /\ WF_vars(Stop)

\* Safety: readers and writers are never active at the same time.
Safety ==
  /\ readers # {} => writers = {}
  /\ writers # {} => readers = {}

\* Liveness: every process eventually reads and eventually writes.
Liveness ==
  \A p \in Process: (p \in readers) ~> (p \in readers) /\ (p \in writers) ~> (p \in writers)

====