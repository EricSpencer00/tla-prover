---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

(* the set of actors – the .cfg file will replace n with a concrete set *)
n == 1 .. NumActors
Proc == n

(* a request record *)
Request == [proc: Proc, mode: {"read", "write"}]

VARIABLES Readers, Writers, Queue

(* ------------------------------------------------------------------- *)
(* Helper predicate *)
InQueue(p) == \E r \in Queue: r.proc = p

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

(* ------------------------------------------------------------------- *)
(* Actions *)

RequestRead(p) ==
    /\ p \in Proc
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~InQueue(p)
    /\ Queue' = Append(Queue, [proc |-> p, mode |-> "read"])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in Proc
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~InQueue(p)
    /\ Queue' = Append(Queue, [proc |-> p, mode |-> "write"])
    /\ UNCHANGED <<Readers, Writers>>

ProcessRead ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ Head(Queue).mode = "read"
    /\ Readers' = Readers \cup {Head(Queue).proc}
    /\ Writers' = Writers
    /\ Queue'   = Tail(Queue)

ProcessWrite ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ Head(Queue).mode = "write"
    /\ Readers = {}
    /\ Readers' = Readers
    /\ Writers' = Writers \cup {Head(Queue).proc}
    /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Readers' = Readers
          /\ Writers' = Writers \ {p}
    /\ UNCHANGED Queue

Next ==
    \/ \E p \in Proc: RequestRead(p)
    \/ \E p \in Proc: RequestWrite(p)
    \/ \E p \in Proc: Stop(p)
    \/ ProcessRead
    \/ ProcessWrite

(* ------------------------------------------------------------------- *)
(* Specification *)
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>>

(* ------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ Readers \subseteq Proc
    /\ Writers \subseteq Proc
    /\ Queue \in Seq(Request)

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ (Writers = {} \/ \E w \in Proc: Writers = {w})

(* ------------------------------------------------------------------- *)
(* Liveness property *)

Liveness ==
    \A p \in Proc :
        /\ <> (p \in Readers)
        /\ <> (p \in Writers)
        /\ [] ( (p \in Readers) => <> (p \notin Readers) )
        /\ [] ( (p \in Writers) => <> (p \notin Writers) )
=============================================================================