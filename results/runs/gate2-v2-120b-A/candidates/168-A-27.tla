---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* ------------------------------------------------------------------------- *)
(*  Derived sets                                                             *)
(* ------------------------------------------------------------------------- *)
Actors == 1 .. NumActors

Request == {"R", "W"}

(* ------------------------------------------------------------------------- *)
(*  Variables                                                               *)
(* ------------------------------------------------------------------------- *)
VARIABLES readers, writers, queue

(* ------------------------------------------------------------------------- *)
(*  State definitions                                                       *)
(* ------------------------------------------------------------------------- *)
vars == << readers, writers, queue >>

(* ------------------------------------------------------------------------- *)
(*  Initialization                                                          *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

(* ------------------------------------------------------------------------- *)
(*  Helper definitions                                                      *)
(* ------------------------------------------------------------------------- *)
Enq(q, req) == Append(q, req)

Front(q) == q[1]

Tail(q) == SubSeq(q, 2, Len(q))

IsFull(q) == FALSE   \* No explicit bound on the queue length

(* ------------------------------------------------------------------------- *)
(*  Actions                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Request to read: proc not already waiting to read *)
RequestRead(proc) ==
    /\ proc \in Actors
    /\ \A i \in 1..Len(queue) : ~(queue[i].proc = proc /\ queue[i].type = "R")
    /\ queue' = Enq(queue, [type |-> "R", proc |-> proc])
    /\ UNCHANGED <<readers, writers>>

(* Request to write: proc not already waiting to write *)
RequestWrite(proc) ==
    /\ proc \in Actors
    /\ \A i \in 1..Len(queue) : ~(queue[i].proc = proc /\ queue[i].type = "W")
    /\ queue' = Enq(queue, [type |-> "W", proc |-> proc])
    /\ UNCHANGED <<readers, writers>>

(* Begin reading or writing based on queue head *)
ProcessQueue ==
    /\ Len(queue) > 0
    /\ writers = {}                     \* no writer active
    /\ LET head == Front(queue) IN
       IF head.type = "R" THEN
          /\ readers' = readers \cup {head.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE   \* write request
          /\ readers = {}                \* no readers active
          /\ writers' = writers \cup {head.proc}
          /\ queue'   = Tail(queue)
    /\ UNCHANGED <<>>

(* Any active reader may stop *)
StopRead ==
    \E proc \in readers :
        /\ readers' = readers \ {proc}
        /\ UNCHANGED <<writers, queue>>

(* Any active writer may stop *)
StopWrite ==
    \E proc \in writers :
        /\ writers' = writers \ {proc}
        /\ UNCHANGED <<readers, queue>>

(* ------------------------------------------------------------------------- *)
(*  Next-state relation                                                     *)
(* ------------------------------------------------------------------------- *)
Next ==
    \/ \E proc \in Actors : RequestRead(proc)
    \/ \E proc \in Actors : RequestWrite(proc)
    \/ ProcessQueue
    \/ StopRead
    \/ StopWrite

(* ------------------------------------------------------------------------- *)
(*  Specification                                                           *)
(* ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(*  Type correctness (optional but useful)                                  *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ writers \subseteq {}
    /\ queue \in Seq([type : Request, proc : Actors])

(* ------------------------------------------------------------------------- *)
(*  Safety invariant: no concurrent readers and writers, at most one writer   *)
(* ------------------------------------------------------------------------- *)
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

(* ------------------------------------------------------------------------- *)
(*  Liveness properties (placeholders; actual properties are defined in .cfg) *)
(* ------------------------------------------------------------------------- *)

Termination ==
    <> (readers = {} /\ writers = {} /\ Len(queue) = 0)

(* ------------------------------------------------------------------------- *)
(*  THEOREMS (optional, not required by the .cfg)                           *)
(* ------------------------------------------------------------------------- *)

=============================================================================