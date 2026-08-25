---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

(* set of actor identifiers *)
n == 1..NumActors

VARIABLES readers, writers, queue

(* a request in the waiting queue *)
Request == [type : {"read", "write"}, proc : n]

(* initial state *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

(* helper: is a process already queued? *)
Queued(p) == p \in { r.proc : r \in SeqToSet(queue) }

(* a process requests read access *)
RequestRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ ~Queued(p)
    /\ readers' = readers
    /\ writers' = writers
    /\ queue'   = Append(queue, [type |-> "read", proc |-> p])

(* a process requests write access *)
RequestWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ ~Queued(p)
    /\ readers' = readers
    /\ writers' = writers
    /\ queue'   = Append(queue, [type |-> "write", proc |-> p])

(* the first queued read request is granted *)
ProcessRead ==
    /\ Len(queue) > 0
    /\ queue[1].type = "read"
    /\ writers = {}
    /\ readers' = readers \cup {queue[1].proc}
    /\ writers' = writers
    /\ queue'   = Tail(queue)

(* the first queued write request is granted *)
ProcessWrite ==
    /\ Len(queue) > 0
    /\ queue[1].type = "write"
    /\ readers = {}
    /\ readers' = readers
    /\ writers' = writers \cup {queue[1].proc}
    /\ queue'   = Tail(queue)

(* a reader voluntarily stops *)
StopRead(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ writers' = writers
    /\ queue'   = queue

(* a writer voluntarily stops *)
StopWrite(p) ==
    /\ p \in writers
    /\ readers' = readers
    /\ writers' = writers \ {p}
    /\ queue'   = queue

(* next-state relation *)
Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ \E p \in n: StopRead(p)
    \/ \E p \in n: StopWrite(p)
    \/ ProcessRead
    \/ ProcessWrite

vars == <<readers, writers, queue>>

(* specification *)
Spec == Init /\ [][Next]_vars

(* type correctness invariant *)
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ queue   \in Seq(Request)

(* safety properties *)
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

(* liveness property *)
Liveness ==
    \A p \in n: (<> (p \in readers) /\ <> (p \in writers))

=============================================================================