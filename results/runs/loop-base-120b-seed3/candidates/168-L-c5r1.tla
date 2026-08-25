---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* the set of actor identifiers, overridden by the .cfg file if needed *)
n == 1 .. NumActors

VARIABLES readers, writers, queue

(* ---------------------------------------------------------------------- *)
(* Types *)

RequestType == {"R", "W"}

Request == [proc : n, mode : RequestType]

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

(* ---------------------------------------------------------------------- *)
(* Actions *)

RequestRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p)
    /\ queue' = Append(queue, [proc |-> p, mode |-> "R"])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p)
    /\ queue' = Append(queue, [proc |-> p, mode |-> "W"])
    /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
    \/ /\ queue # <<>>
       /\ writers = {}
       /\ LET q == Head(queue) IN
            /\ q.mode = "R"
            /\ readers' = readers \cup {q.proc}
            /\ queue'   = Tail(queue)
            /\ UNCHANGED writers
    \/ /\ queue # <<>>
       /\ writers = {}
       /\ LET q == Head(queue) IN
            /\ q.mode = "W"
            /\ readers' = {}
            /\ writers' = {q.proc}
            /\ queue'   = Tail(queue)

StopReading(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED <<writers, queue>>

StopWriting(p) ==
    /\ p \in writers
    /\ writers' = {}
    /\ UNCHANGED <<readers, queue>>

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n : StopReading(p)
    \/ \E p \in n : StopWriting(p)

vars == <<readers, writers, queue>>

(* ---------------------------------------------------------------------- *)
(* Specification *)

Spec ==
    Init
    /\ [][Next]_vars
    /\ \A p \in n : WF_vars(RequestRead(p))
    /\ \A p \in n : WF_vars(RequestWrite(p))
    /\ WF_vars(ProcessQueue)
    /\ \A p \in n : WF_vars(StopReading(p))
    /\ \A p \in n : WF_vars(StopWriting(p))

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ Cardinality(writers) <= 1
    /\ queue \in Seq(Request)

Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

(* ---------------------------------------------------------------------- *)
(* Liveness property *)

Liveness ==
    \A p \in n :
        ( <> (p \in readers)
          /\ [] (p \in readers => <> (p \notin readers))
          /\ <> (p \in writers)
          /\ [] (p \in writers => <> (p \notin writers)) )

====