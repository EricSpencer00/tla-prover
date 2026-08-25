---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

(* the set of actor identifiers *)
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

(*-----------------------------------------------------------------
   Types
-----------------------------------------------------------------*)
Req == [type : {"read", "write"}, proc : n]

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Req)

(*-----------------------------------------------------------------
   Initial state
-----------------------------------------------------------------*)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

(*-----------------------------------------------------------------
   Actions
-----------------------------------------------------------------*)
RequestRead(p) ==
    /\ p \in n
    /\ \A r \in Queue : r.proc # p
    /\ Queue' = Append(Queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED << Readers, Writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ \A r \in Queue : r.proc # p
    /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED << Readers, Writers >>

ProcessQueue ==
    /\ Queue # <<>>
    /\ Writers = {}
    LET front == Head(Queue) IN
        ( /\ (front.type = "read")
            /\ Readers' = Readers \cup {front.proc}
            /\ Writers' = Writers
         \/ /\ (front.type = "write")
            /\ Readers = {}
            /\ Readers' = Readers
            /\ Writers' = Writers \cup {front.proc} )
    /\ Queue' = Tail(Queue)
    /\ UNCHANGED << >>

Stop(p) ==
    /\ p \in n
    /\ (p \in Readers) \/ (p \in Writers)
    /\ IF p \in Readers THEN
           Readers' = Readers \ {p}
           /\ Writers' = Writers
       ELSE
           Readers' = Readers
           /\ Writers' = Writers \ {p}
    /\ UNCHANGED << Queue >>

(*-----------------------------------------------------------------
   Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n : Stop(p)

(*-----------------------------------------------------------------
   Fairness
-----------------------------------------------------------------*)
RequestReadAction == \E p \in n : RequestRead(p)
RequestWriteAction == \E p \in n : RequestWrite(p)
StopAction == \E p \in n : Stop(p)

Spec ==
    Init /\
    [][Next]_<<Readers, Writers, Queue>> /\
    WF_vars(RequestReadAction) /\
    WF_vars(RequestWriteAction) /\
    WF_vars(ProcessQueue) /\
    WF_vars(StopAction)

(*-----------------------------------------------------------------
   Invariants
-----------------------------------------------------------------*)
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

(*-----------------------------------------------------------------
   Liveness property
-----------------------------------------------------------------*)
Liveness ==
    \A p \in n :
        <> (p \in Readers) /\ <> (p \in Writers)

====