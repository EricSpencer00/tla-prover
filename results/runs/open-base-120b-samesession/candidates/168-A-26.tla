---- MODULE ReadersWriters ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT NumActors

(*--------------------------------------------------------------------*)
(*  Definition of the actor set (substituted for NumActors in .cfg)   *)
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

(*--------------------------------------------------------------------*)
(*  Types                                                             *)
ReaderType == {"read","write"}
Request == [type : ReaderType, proc : n]

(*--------------------------------------------------------------------*)
(*  Initial state                                                     *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

(*--------------------------------------------------------------------*)
(*  Helper predicates                                                 *)
PendingRead(p) ==
    \E i \in DOMAIN Queue :
        Queue[i].type = "read" /\ Queue[i].proc = p

PendingWrite(p) ==
    \E i \in DOMAIN Queue :
        Queue[i].type = "write" /\ Queue[i].proc = p

(*--------------------------------------------------------------------*)
(*  Actions                                                           *)
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~ PendingRead(p)
    /\ Queue' = Append(Queue, [type |-> "read",  proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~ PendingWrite(p)
    /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

Begin ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ LET front == Queue[1] IN
       /\ front.type = "read"
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       \/ ( front.type = "write"
            /\ Readers = {}
            /\ Writers' = Writers \cup {front.proc}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue) )
    /\ UNCHANGED <<>>

Stop(p) ==
    /\ p \in n
    /\ (p \in Readers \/ p \in Writers)
    /\ IF p \in Readers
          THEN Readers' = Readers \ {p}
               /\ Writers' = Writers
          ELSE Readers' = Readers
               /\ Writers' = Writers \ {p}
    /\ UNCHANGED Queue

(*--------------------------------------------------------------------*)
(*  Composite actions for fairness                                    *)
ReqRead  == \E p \in n : RequestRead(p)
ReqWrite == \E p \in n : RequestWrite(p)
StopAct  == \E p \in n : Stop(p)

(*--------------------------------------------------------------------*)
(*  Next-state relation                                                *)
Next ==
    \/ ReqRead
    \/ ReqWrite
    \/ Begin
    \/ StopAct

vars == <<Readers, Writers, Queue>>

(*--------------------------------------------------------------------*)
(*  Specification                                                     *)
Spec ==
    Init /\ [][Next]_vars
         /\ WF_vars(ReqRead)
         /\ WF_vars(ReqWrite)
         /\ WF_vars(Begin)
         /\ WF_vars(StopAct)

(*--------------------------------------------------------------------*)
(*  Type correctness invariant                                        *)
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Request)

(*--------------------------------------------------------------------*)
(*  Safety invariant                                                  *)
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

(*--------------------------------------------------------------------*)
(*  Liveness property                                                 *)
Liveness ==
    \A p \in n :
        ( <> (p \in Readers) )
        /\ ( <> (p \in Writers) )
        /\ [] (p \in Readers => <> (p \notin Readers))
        /\ [] (p \in Writers => <> (p \notin Writers))

====