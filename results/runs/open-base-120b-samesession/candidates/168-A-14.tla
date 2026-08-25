---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* ----------------------------------------------------------------------
   The set of actor identifiers.
   The .cfg file substitutes the constant NumActors with the operator n.
---------------------------------------------------------------------- *)
n == 1 .. NumActors

VARIABLES readers, writers, queue

(* ----------------------------------------------------------------------
   Types
---------------------------------------------------------------------- *)
QueueElem == [type : {"read", "write"}, proc : n]

TypeOK ==
  /\ readers \subseteq n
  /\ writers \subseteq n
  /\ Disjoint(readers, writers)
  /\ queue \in Seq(QueueElem)

(* ----------------------------------------------------------------------
   Initial state
---------------------------------------------------------------------- *)
Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue   = << >>

(* ----------------------------------------------------------------------
   Actions
---------------------------------------------------------------------- *)

RequestRead(p) ==
  /\ p \in n
  /\ p \notin readers
  /\ p \notin writers
  /\ p \notin { q.proc : q \in queue }
  /\ queue' = Append(queue, [type |-> "read", proc |-> p])
  /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
  /\ p \in n
  /\ p \notin readers
  /\ p \notin writers
  /\ p \notin { q.proc : q \in queue }
  /\ queue' = Append(queue, [type |-> "write", proc |-> p])
  /\ UNCHANGED << readers, writers >>

ProcessQueue ==
  LET h == Head(queue) IN
  /\ queue # << >>
  /\ writers = {}                               \* no writer currently active
  /\ IF h.type = "read" THEN
        /\ readers' = readers \cup {h.proc}
        /\ writers' = writers
        /\ queue'   = Tail(queue)
     ELSE
        /\ h.type = "write"
        /\ readers = {}                         \* no readers before a write
        /\ readers' = readers
        /\ writers' = writers \cup {h.proc}
        /\ queue'   = Tail(queue)

Stop(p) ==
  /\ p \in readers \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in n: RequestRead(p)
  \/ \E p \in n: RequestWrite(p)
  \/ \E p \in n: Stop(p)
  \/ ProcessQueue

(* ----------------------------------------------------------------------
   Specification
---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<readers, writers, queue>>

(* ----------------------------------------------------------------------
   Safety invariant
---------------------------------------------------------------------- *)
Safety ==
  /\ (readers = {} \/ writers = {})
  /\ Cardinality(writers) <= 1

(* ----------------------------------------------------------------------
   Liveness property
---------------------------------------------------------------------- *)
Liveness ==
  /\ \A p \in n: <> (p \in readers)
  /\ \A p \in n: <> (p \in writers)
  /\ \A p \in n: [] (p \in readers => <> (p \notin readers))
  /\ \A p \in n: [] (p \in writers => <> (p \notin writers))

====