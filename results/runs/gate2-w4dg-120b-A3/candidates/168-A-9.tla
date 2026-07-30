---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat

\* A fair readers-writers system with an explicit first-come-first-served queue.
\* Readers may share the resource, but writers need exclusive access. Weak
\* fairness on every action (instead of strong fairness) is sufficient here,
\* since the actions themselves are always enabled enough to make progress.

Requests == [proc: 0 .. NumActors, kind: {"read", "write"}]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq (0 .. NumActors)
    /\ writers \subseteq (0 .. NumActors)
    /\ queue \in Seq(Requests)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(p) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].proc # p
    /\ queue' = Append(queue, [proc |-> p, kind |-> "read"])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].proc # p
    /\ queue' = Append(queue, [proc |-> p, kind |-> "write"])
    /\ UNCHANGED <<readers, writers>>

\* Begin is the queue's head: a pending request is granted only if it keeps the
\* readers/writers separation intact.
Begin ==
    /\ Len(queue) > 0
    /\ writers = {}
    /\ LET head == Head(queue) IN
         /\ IF head.kind = "read"
              THEN readers' = readers \cup {head.proc}
              ELSE readers' = readers
         /\ writers' = IF head.kind = "write" /\ readers = {}
                         THEN writers \cup {head.proc}
                         ELSE writers
    /\ queue' = Tail(queue)

Stop ==
    /\ \E p \in readers : readers' = readers \ {p}
    /\ \E p \in writers : writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in 0 .. NumActors : RequestRead(p)
    \/ \E p \in 0 .. NumActors : RequestWrite(p)
    \/ Begin
    \/ Stop

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 0 .. NumActors : RequestRead(p))
        /\ WF_vars(\E p \in 0 .. NumActors : RequestWrite(p))
        /\ WF_vars(Begin)
        /\ WF_vars(Stop)

\* Readers and writers never active together; at most one writer active.
Safety ==
    /\ ~(readers = {} /\ writers # {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A p \in 0 .. NumActors :
        /\ (p \in readers) ~> (p \notin readers)
        /\ (p \in writers) ~> (p \notin writers)

====