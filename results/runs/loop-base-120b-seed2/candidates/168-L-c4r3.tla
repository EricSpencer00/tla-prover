---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-------------------------------------------------------------------*)
(*  Constants                                                          *)
(*-------------------------------------------------------------------*)

CONSTANT NumActors   \* (may be used by the configuration file)
CONSTANT n           \* the finite set of actor identifiers; will be
                     \* supplied by the .cfg file (e.g., n = 1..NumActors)

VARIABLES Readers, Writers, Queue

(*-------------------------------------------------------------------*)
(*  Types and state predicates                                         *)
(*-------------------------------------------------------------------*)

RequestRec == [proc: n, type: {"Read", "Write"}]

Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

TypeOK ==
    /\ Readers \in SUBSET n
    /\ Writers \in SUBSET n
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq(RequestRec)

(*-------------------------------------------------------------------*)
(*  Actions                                                            *)
(*-------------------------------------------------------------------*)

RequestRead(p) ==
    /\ p \in n
    /\ ~(\E q \in Queue: q.proc = p)          \* p is not already waiting
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "Read"])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ ~(\E q \in Queue: q.proc = p)          \* p is not already waiting
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "Write"])
    /\ UNCHANGED <<Readers, Writers>>

Process ==
    /\ Queue # <<>>                           \* queue non‑empty
    /\ Writers = {}                           \* no writer currently active
    /\ LET q == Head(Queue) IN
         IF q.type = "Read" THEN
            /\ Readers' = Readers \cup {q.proc}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue)
         ELSE                                   \* write request
            /\ Readers = {}                    \* ensure no readers are active
            /\ Readers' = Readers
            /\ Writers' = {q.proc}
            /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Readers' = Readers
          /\ Writers' = {}
    /\ UNCHANGED Queue

Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ Process
    \/ \E p \in n: Stop(p)

(*-------------------------------------------------------------------*)
(*  Specification                                                      *)
(*-------------------------------------------------------------------*)

Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>>

(*-------------------------------------------------------------------*)
(*  Safety property                                                    *)
(*-------------------------------------------------------------------*)

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

(*-------------------------------------------------------------------*)
(*  Liveness property                                                  *)
(*-------------------------------------------------------------------*)

Liveness ==
    /\ \A p \in n: <> (p \in Readers)          \* every process eventually reads
    /\ \A p \in n: <> (p \in Writers)          \* every process eventually writes
    /\ []<>(\A p \in n: p \notin Readers)      \* active readers eventually stop
    /\ []<>(\A p \in n: p \notin Writers)      \* active writers eventually stop

(*-------------------------------------------------------------------*)
(*  Theorems (optional)                                                *)
(*-------------------------------------------------------------------*)

THEOREM TypeOKInv == Spec => []TypeOK
THEOREM SafetyInv == Spec => []Safety

====