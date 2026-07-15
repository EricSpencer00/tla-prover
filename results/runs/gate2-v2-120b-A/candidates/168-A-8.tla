---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANT NumActors

VARIABLES readers, writers, queue

(* --type definitions ------------------------------------------------------ *)
ReaderSet == 1 .. NumActors
WriterSet == 1 .. NumActors
ReqType   == {"read", "write"}
Request   == [type : ReqType, proc : 1..NumActors]

(* --state variables -------------------------------------------------------- *)
vars == << readers, writers, queue >>

(* --initial state ---------------------------------------------------------- *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

(* --actions --------------------------------------------------------------- *)

RequestRead(proc) ==
    /\ proc \in ReaderSet
    /\ \A r \in queue: r.proc # proc      \* not already waiting
    /\ queue' = Append(queue, [type |-> "read", proc |-> proc])
    /\ UNCHANGED << readers, writers >>

RequestWrite(proc) ==
    /\ proc \in WriterSet
    /\ \A r \in queue: r.proc # proc      \* not already waiting
    /\ queue' = Append(queue, [type |-> "write", proc |-> proc])
    /\ UNCHANGED << readers, writers >>

BeginAction ==
    /\ queue # << >>
    /\ LET front == Head(queue) IN
       /\ writers = {}                     \* no writer currently active
       /\ IF front.type = "read" THEN
            /\ readers' = readers \cup { front.proc }
            /\ writers' = {}
          ELSE
            /\ readers = {}
            /\ writers' = { front.proc }
    /\ queue' = Tail(queue)
    /\ UNCHANGED readers \cup writers  \* the other set unchanged

StopActivity(proc) ==
    /\ proc \in readers \/ proc \in writers
    /\ readers' = readers \ {proc}
    /\ writers' = writers \ {proc}
    /\ UNCHANGED queue

Next ==
    \/ \E proc \in ReaderSet: RequestRead(proc)
    \/ \E proc \in WriterSet: RequestWrite(proc)
    \/ BeginAction
    \/ \E proc \in (readers \cup writers): StopActivity(proc)

(* --specification ---------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* --type correctness invariant -------------------------------------------- *)
TypeOK ==
    /\ readers \subseteq ReaderSet
    /\ writers \subseteq WriterSet
    /\ writers \subseteq 1..NumActors
    /\ queue \in Seq(Request)

(* --safety invariant ------------------------------------------------------- *)
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

(* --liveness property ------------------------------------------------------ *)
Liveness ==
    /\ \A p \in ReaderSet: <> (p \in readers)
    /\ \A p \in WriterSet: <> (p \in writers)

=============================================================================