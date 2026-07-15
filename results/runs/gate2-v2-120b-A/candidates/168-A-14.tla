---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(*---------------------------------------------------------------------------*)
(*   Derived sets                                                            *)
(*---------------------------------------------------------------------------*)
Actors == 1 .. NumActors

ReadRequest == "Read"
WriteRequest == "Write"

Request == [type : {ReadRequest, WriteRequest},
            proc : Actors]

(*---------------------------------------------------------------------------*)
(*   State variables                                                        *)
(*---------------------------------------------------------------------------*)
VARIABLES reading, writing, queue

(*---------------------------------------------------------------------------*)
(*   Type invariant (for sanity checking)                                   *)
(*---------------------------------------------------------------------------*)
TypeOK ==
    /\ reading \in SUBSET Actors
    /\ writing \in SUBSET Actors
    /\ queue   \in Seq(Request)

(*---------------------------------------------------------------------------*)
(*   Initial state                                                          *)
(*---------------------------------------------------------------------------*)
Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue   = <<>>

(*---------------------------------------------------------------------------*)
(*   Actions                                                                *)
(*---------------------------------------------------------------------------*)
RequestRead(proc) ==
    /\ proc \in Actors
    /\ \A i \in 1 .. Len(queue): ~(queue[i].type = ReadRequest /\ queue[i].proc = proc)
    /\ queue' = Append(queue, [type |-> ReadRequest, proc |-> proc])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(proc) ==
    /\ proc \in Actors
    /\ \A i \in 1 .. Len(queue): ~(queue[i].type = WriteRequest /\ queue[i].proc = proc)
    /\ queue' = Append(queue, [type |-> WriteRequest, proc |-> proc])
    /\ UNCHANGED <<reading, writing>>

BeginAct ==
    /\ Len(queue) > 0
    /\ writing = {}               \* no writer currently active
    /\ LET front == queue[1] IN
       IF front.type = ReadRequest THEN
          /\ reading' = reading \cup {front.proc}
          /\ writing' = {}
          /\ queue'   = Tail(queue)
       ELSE
          /\ reading = {}        \* no readers currently active
          /\ writing' = {front.proc}
          /\ queue'   = Tail(queue)

StopAct ==
    /\ \E proc \in reading \cup writing :
         /\ IF proc \in reading
               THEN reading' = reading \ {proc}
               ELSE UNCHANGED reading
         /\ IF proc \in writing
               THEN writing' = writing \ {proc}
               ELSE UNCHANGED writing
         /\ UNCHANGED queue

Next ==
    \/ \E proc \in Actors: RequestRead(proc)
    \/ \E proc \in Actors: RequestWrite(proc)
    \/ BeginAct
    \/ \E proc \in reading \cup writing: StopAct

(*---------------------------------------------------------------------------*)
(*   Specification                                                          *)
(*---------------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<reading, writing, queue>>

(*---------------------------------------------------------------------------*)
(*   Safety invariant (the required invariant)                              *)
(*---------------------------------------------------------------------------*)
Safety ==
    /\ (writing = {}) \/ (reading = {})
    /\ Cardinality(writing) <= 1

=============================================================================