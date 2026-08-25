---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

(*--------------------------------------------------------------------
  Derived constant: the set of actor identifiers
--------------------------------------------------------------------*)
n == 1..NumActors

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES Readers, Writers, Queue

vars == << Readers, Writers, Queue >>

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
ReadWriteType == {"read", "write"}

Request == [type : ReadWriteType, proc : n]

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Waiting(p) ==
    \E i \in 1..Len(Queue) : Queue[i].proc = p

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

RequestRead(p) ==
    /\ p \in n
    /\ ~ (p \in Readers \/ p \in Writers \/ Waiting(p))
    /\ Queue' = Queue \o << [type |-> "read",  proc |-> p] >>
    /\ UNCHANGED << Readers, Writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ ~ (p \in Readers \/ p \in Writers \/ Waiting(p))
    /\ Queue' = Queue \o << [type |-> "write", proc |-> p] >>
    /\ UNCHANGED << Readers, Writers >>

BeginRead ==
    /\ Len(Queue) > 0
    /\ Queue[1].type = "read"
    /\ Readers' = Readers \cup { Queue[1].proc }
    /\ Writers' = Writers
    /\ Queue'   = Tail(Queue)

BeginWrite ==
    /\ Len(Queue) > 0
    /\ Queue[1].type = "write"
    /\ Readers = {}            \* no readers currently
    /\ Writers = {}            \* no writer currently
    /\ Writers' = Writers \cup { Queue[1].proc }
    /\ Readers' = Readers
    /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in n
    /\ (p \in Readers \/ p \in Writers)
    /\ Readers' = Readers \ {p}
    /\ Writers' = Writers \ {p}
    /\ UNCHANGED Queue

Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ \E p \in n : Stop(p)
    \/ BeginRead
    \/ BeginWrite

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq(Request)

Safety ==
    /\ (Readers = {} \/ Writers = {})
    /\ Cardinality(Writers) <= 1

(*--------------------------------------------------------------------
  Liveness property
--------------------------------------------------------------------*)
Liveness ==
    \A p \in n :
        (<> (p \in Readers))            /\* eventually reads *
        (<> (p \in Writers))            /\* eventually writes *
        ([] (p \in Readers => <> (p \notin Readers))) /\* readers stop *
        ([] (p \in Writers => <> (p \notin Writers)))   \* writers stop *

====