---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* ---------------------------------------------------------------------- *)
(* Constants *)
(* ---------------------------------------------------------------------- *)
ActorSet == 1..NumActors

(* ---------------------------------------------------------------------- *)
(* Types *)
(* ---------------------------------------------------------------------- *)
ReqType == {"read", "write"}
Request == [type : ReqType, proc : ActorSet]

(* ---------------------------------------------------------------------- *)
(* Variables *)
(* ---------------------------------------------------------------------- *)
VARIABLES readers, writers, queue

(* ---------------------------------------------------------------------- *)
(* Type invariant (helps TLC) *)
(* ---------------------------------------------------------------------- *)
ReadersInSet == readers \subseteq ActorSet
WritersInSet == writers \subseteq ActorSet
QueueOK == /\ queue \in Seq(Request)
            /\ Len(queue) <= NumActors
            /\ \A i \in 1..Len(queue) : queue[i].proc \in ActorSet

(* ---------------------------------------------------------------------- *)
(* Initial state *)
(* ---------------------------------------------------------------------- *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

(* ---------------------------------------------------------------------- *)
(* Actions *)
(* ---------------------------------------------------------------------- *)

(* 1. Request to read *)
RequestRead(proc) ==
    /\ proc \in ActorSet
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = proc /\ queue[i].type = "read")
    /\ queue' = Append(queue, [type |-> "read", proc |-> proc])
    /\ UNCHANGED << readers, writers >>

(* 2. Request to write *)
RequestWrite(proc) ==
    /\ proc \in ActorSet
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = proc /\ queue[i].type = "write")
    /\ queue' = Append(queue, [type |-> "write", proc |-> proc])
    /\ UNCHANGED << readers, writers >>

(* 3. Begin reading or writing *)
ProcessQueue ==
    /\ Len(queue) > 0
    /\ LET front == queue[1] IN
       IF front.type = "read" THEN
          /\ writers = {}               \* no writer active
          /\ readers' = readers \cup {front.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE
          /\ front.type = "write"
          /\ readers = {}               \* no readers active
          /\ writers' = writers \cup {front.proc}
          /\ readers' = readers
          /\ queue'   = Tail(queue)

(* 4. Stop reading *)
StopRead(proc) ==
    /\ proc \in readers
    /\ readers' = readers \ {proc}
    /\ UNCHANGED << writers, queue >>

(* 5. Stop writing *)
StopWrite(proc) ==
    /\ proc \in writers
    /\ writers' = writers \ {proc}
    /\ UNCHANGED << readers, queue >>

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)
(* ---------------------------------------------------------------------- *)
Next ==
    \/ \E p \in ActorSet : RequestRead(p)
    \/ \E p \in ActorSet : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in ActorSet : StopRead(p)
    \/ \E p \in ActorSet : StopWrite(p)

(* ---------------------------------------------------------------------- *)
(* Specification *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<readers, writers, queue>>

(* ---------------------------------------------------------------------- *)
(* Safety invariant: at most one writer and no concurrent readers/writers *)
(* ---------------------------------------------------------------------- *)
Safety ==
    /\ Cardinality(writers) <= 1
    /\ (writers = {} \/ readers = {})

(* ---------------------------------------------------------------------- *)
(* Liveness properties (one per actor, read and write) *)
(* ---------------------------------------------------------------------- *)
Liveness ==
    /\ \A p \in ActorSet :
          <> (p \in readers)   \* eventually p reads
    /\ \A p \in ActorSet :
          <> (p \in writers)   \* eventually p writes
    /\ \A p \in ActorSet :
          [] (p \in readers => <> (p \notin readers)) \* any reader eventually stops
    /\ \A p \in ActorSet :
          [] (p \in writers => <> (p \notin writers)) \* any writer eventually stops

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant (optional but useful) *)
(* ---------------------------------------------------------------------- *)
TypeOK == /\ ReadersInSet
          /\ WritersInSet
          /\ QueueOK

====