---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

(*--------------------------------------------------------------------*)
(*  Constants (to be bound by the .cfg file)                           *)
(*--------------------------------------------------------------------*)
CONSTANT N, MaxNat, Nat   \* Nat is the overridden natural-number set

(*--------------------------------------------------------------------*)
(*  Derived sets and constants                                         *)
(*--------------------------------------------------------------------*)
Proc == 1 .. N
Range == 0 .. MaxNat

(*--------------------------------------------------------------------*)
(*  Variable declarations                                              *)
(*--------------------------------------------------------------------*)
VARIABLES pc, ticket, choosing

(*--------------------------------------------------------------------*)
(*  Type correctness predicate                                         *)
(*--------------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> {"idle", "wait", "cs", "exit"}]
    /\ ticket \in [Proc -> Range]
    /\ choosing \in [Proc -> BOOLEAN]

(*--------------------------------------------------------------------*)
(*  Initial state (all processes idle, ticket 0, not choosing)        *)
(*--------------------------------------------------------------------*)
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]
    /\ TypeOK

(*--------------------------------------------------------------------*)
(*  Actions                                                            *)
(*--------------------------------------------------------------------*)
Choose(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = 
        ( IF i = 1 THEN 1 ELSE ticket[i-1] + 1 ) % (MaxNat+1) ]
    /\ UNCHANGED << >>

Number(i) ==
    /\ pc[i] = "wait"
    /\ choosing[i] = TRUE
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED << pc, ticket >>

Enter(i) ==
    /\ pc[i] = "wait"
    /\ \A j \in Proc :
          (j # i) => 
            ( (choosing[j]) 
              \/ (ticket[j] # 0 /\ 
                 ( ticket[j] < ticket[i] \/ 
                   (ticket[j] = ticket[i] /\ j < i) ) ) )
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << ticket, choosing >>

Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED << ticket, choosing >>

Reset(i) ==
    /\ pc[i] = "exit"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED << choosing >>

Action ==
    \E i \in Proc :
        Choose(i) \/ Number(i) \/ Enter(i) \/ Exit(i) \/ Reset(i)

Next ==
    Action

(*--------------------------------------------------------------------*)
(*  Safety invariant: mutual exclusion                               *)
(*--------------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

(*--------------------------------------------------------------------*)
(*  Full inductive invariant (type correctness + safety)              *)
(*--------------------------------------------------------------------*)
Inv == TypeOK /\ MutualExclusion

(*--------------------------------------------------------------------*)
(*  Specification (inductive)                                         *)
(*--------------------------------------------------------------------*)
ISpec == Init /\ [][Next]_<<pc, ticket, choosing>>

=============================================================================