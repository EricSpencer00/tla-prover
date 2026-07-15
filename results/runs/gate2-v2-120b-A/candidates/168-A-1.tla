---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
Proc == 1..NumActors

ReadReq == "READ"
WriteReq == "WRITE"

ReqType == {ReadReq, WriteReq}

(* ----------------------------------------------------------------------
   Type invariant (for debugging)
   ---------------------------------------------------------------------- *)
Request == [type : ReqType, proc : Proc]

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES readers, writers, queue

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
ReadersSet == readers
WritersSet == writers
QueueSeq == queue

Active == readers \cup writers

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

RequestRead(i) ==
    /\ i \in Proc
    /\ i \notin { r.proc : r \in Active }
    /\ queue' = Append(queue, [type |-> ReadReq, proc |-> i])
    /\ UNCHANGED << readers, writers >>

RequestWrite(i) ==
    /\ i \in Proc
    /\ i \notin { r.proc : r \in Active }
    /\ queue' = Append(queue, [type |-> WriteReq, proc |-> i])
    /\ UNCHANGED << readers, writers >>

StartRead(i) ==
    /\ queue # << >>
    /\ queue[1].type = ReadReq
    /\ queue[1].proc = i
    /\ writers = {}               \* No writer active
    /\ readers' = readers \cup {i}
    /\ queue' = Tail(queue)
    /\ UNCHANGED writers

StartWrite(i) ==
    /\ queue # << >>
    /\ queue[1].type = WriteReq
    /\ queue[1].proc = i
    /\ readers = {}               \* No readers active
    /\ writers' = writers \cup {i}
    /\ queue' = Tail(queue)
    /\ UNCHANGED readers

Stop(i) ==
    /\ i \in readers
    /\ readers' = readers \ {i}
    /\ UNCHANGED << writers, queue >>

StopWrite(i) ==
    /\ i \in writers
    /\ writers' = writers \ {i}
    /\ UNCHANGED << readers, queue >>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E i \in Proc: RequestRead(i)
    \/ \E i \in Proc: RequestWrite(i)
    \/ \E i \in Proc: StartRead(i)
    \/ \E i \in Proc: StartWrite(i)
    \/ \E i \in Proc: Stop(i)
    \/ \E i \in Proc: StopWrite(i)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<< readers, writers, queue >>

(* ----------------------------------------------------------------------
   Type invariant (optional, named TypeOK)
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ readers \subseteq Proc
    /\ writers \subseteq Proc
    /\ writers \subseteq { i : i \in Proc : i \in writers }  \* trivial but keeps shape
    /\ \A i \in readers: i \notin writers
    /\ queue \in Seq(Request)

(* ----------------------------------------------------------------------
   Safety invariant (named Safety)
   ---------------------------------------------------------------------- *)
Safety ==
    /\ \A i \in writers: i \notin readers
    /\ Cardinality(writers) <= 1

(* ----------------------------------------------------------------------
   Liveness property (named Liveness)
   ---------------------------------------------------------------------- *)
Liveness == 
    /\ \A i \in Proc: <> (i \in readers)   \* eventually i reads
    /\ \A i \in Proc: <> (i \in writers)   \* eventually i writes

====