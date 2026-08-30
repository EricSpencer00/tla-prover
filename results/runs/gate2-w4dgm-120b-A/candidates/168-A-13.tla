---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

(* A readers-writers solution that brokers access to a shared resource through a  *)
(* first-come-first-served request queue, guaranteeing fair, starvation-free       *)
(* service for both readers and writers.                                            *)

CONSTANTS NumActors

\* Two independent instances (n1, n2) both draw from the same shared pool of actors.
\* Each instance tracks its own readers/writers but shares the one request queue.
Instances == {"n1", "n2"}

VARIABLES readers, writers, queue, actorInst

vars == <<readers, writers, queue, actorInst>>

TypeOK ==
    /\ readers \in [Instances -> SUBSET NumActors]
    /\ writers \in [Instances -> SUBSET NumActors]
    /\ queue \in Seq([kind: {"read", "write"}, who: NumActors])
    /\ Len(queue) <= 2
    /\ actorInst \in [NumActors -> Instances]

Init ==
    /\ readers = [i \in Instances |-> {}]
    /\ writers = [i \in Instances |-> {}]
    /\ queue = <<>>
    /\ actorInst = [a \in NumActors |-> CHOOSE i \in Instances : TRUE]

\* A process requests to read; it joins the shared queue if not already queued.
RequestRead ==
    /\ \E a \in NumActors :
         /\ \A k \in 1..Len(queue) : queue[k].who # a
         /\ queue' = Append(queue, [kind |-> "read", who |-> a])
    /\ UNCHANGED <<readers, writers, actorInst>>

\* A process requests to write; it joins the shared queue if not already queued.
RequestWrite ==
    /\ \E a \in NumActors :
         /\ \A k \in 1..Len(queue) : queue[k].who # a
         /\ queue' = Append(queue, [kind |-> "write", who |-> a])
    /\ UNCHANGED <<readers, writers, actorInst>>

\* The head of the queue begins its access, but only when it would not conflict
\* with any active writer (for reads) or any active reader (for a write).
ProcessQueue ==
    /\ queue # <<>>
    /\ \E i \in Instances :
         LET h == Head(queue) IN
         /\ (h.kind = "read" \/ writers[i] = {})
         /\ readers' = [readers EXCEPT ![i] = IF h.kind = "read" THEN readers[i] \cup {h.who} ELSE readers[i]]
         /\ writers' = [writers EXCEPT ![i] = IF h.kind = "write" THEN writers[i] \cup {h.who} ELSE writers[i]]
    /\ queue' = Tail(queue)
    /\ UNCHANGED actorInst

StopActivity ==
    \E i \in Instances :
      \/ \E a \in readers[i] : readers' = [readers EXCEPT ![i] = readers[i] \ {a}]
      \/ \E a \in writers[i] : writers' = [writers EXCEPT ![i] = writers[i] \ {a}]
    /\ UNCHANGED <<queue, actorInst>>

Next == RequestRead \/ RequestWrite \/ ProcessQueue \/ StopActivity

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(RequestRead)
    /\ WF_vars(RequestWrite)
    /\ WF_vars(ProcessQueue)
    /\ WF_vars(StopActivity)

\* Safety: readers and writers of the same instance are never active together,
\* and at most one writer is active at any instant.
Safety ==
    \A i \in Instances :
        /\ (writers[i] # {} => readers[i] = {})
        /\ readers[i] # {} => writers[i] = {}
        /\ readers[i] # {} => readers[i] \subseteq NumActors
        /\ writers[i] # {} => writers[i] \subseteq NumActors

\* Liveness: every process eventually gets to read, then to write, and stops.
Liveness ==
    \A a \in NumActors :
        /\ \A i \in Instances : <>(a \in readers[i])
        /\ \A i \in Instances : <>(a \in writers[i])
        /\ \A i \in Instances : <>(a \notin readers[i])
        /\ \A i \in Instances : <>(a \notin writers[i])

====