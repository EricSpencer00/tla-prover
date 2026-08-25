---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT N, T, F

(*-----------------------------------------------------------------
  Basic sets
-----------------------------------------------------------------*)
Proc == 1..N

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES correct, pc, rcvd, sent

(*-----------------------------------------------------------------
  Derived definitions
-----------------------------------------------------------------*)
faulty == Proc \ correct

(* pc values *)
PCVals == {"NoInit", "Init", "EchoSent", "Accepted", "Faulty"}

(*-----------------------------------------------------------------
  Type correctness (used as invariant)
-----------------------------------------------------------------*)
TypeOK ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> PCVals]
    /\ \A p \in Proc :
          (p \in correct => pc[p] \in {"NoInit", "Init", "EchoSent", "Accepted"})
          /\ (p \in faulty => pc[p] = "Faulty")
    /\ rcvd \in [Proc -> SUBSET Proc]   \* set of senders from which p has received an ECHO
    /\ sent \subseteq correct             \* set of correct processes that have sent an ECHO

(*-----------------------------------------------------------------
  Constraints on constants (used as invariant)
-----------------------------------------------------------------*)
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ faulty = Proc \ correct
    /\ sent = {}
    /\ \A p \in Proc : rcvd[p] = {}
    /\ \A p \in correct :
          \/ pc[p] = "NoInit"
          \/ pc[p] = "Init"
    /\ \A p \in faulty : pc[p] = "Faulty"

(*-----------------------------------------------------------------
  Helper: number of distinct ECHO senders known by p
-----------------------------------------------------------------*)
EchoCount(p) == Cardinality(rcvd[p])

(*-----------------------------------------------------------------
  Action for a single correct process p
-----------------------------------------------------------------*)
Action(p) ==
    /\ p \in correct
    /\ \* Receive an arbitrary set of new ECHO messages (identified by senders)
       LET newRcvd == SUBSET Proc
           newSet   == rcvd[p] \cup newRcvd
           cnt      == Cardinality(newSet)
       IN
         /\ newRcvd \subseteq Proc
         /\ rcvd' = [rcvd EXCEPT ![p] = newSet]
         /\ CASE 
              pc[p] = "Init" ->
                 /\ pc' = [pc EXCEPT ![p] = "Accepted"]
                 /\ sent' = sent \cup {p}
              pc[p] = "NoInit" /\ cnt >= N - T ->
                 /\ pc' = [pc EXCEPT ![p] = "Accepted"]
                 /\ sent' = sent \cup {p}
              pc[p] = "NoInit" /\ cnt >= N - 2 * T /\ cnt < N - T ->
                 /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
                 /\ sent' = sent \cup {p}
              pc[p] = "EchoSent" /\ cnt >= N - T ->
                 /\ pc' = [pc EXCEPT ![p] = "Accepted"]
                 /\ UNCHANGED sent
              OTHER ->
                 /\ pc' = pc
                 /\ UNCHANGED sent
         /\ UNCHANGED <<correct, faulty>>
    /\ UNCHANGED << >>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in correct : Action(p)
    \/ UNCHANGED <<correct, pc, rcvd, sent>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<correct, pc, rcvd, sent>>

(*-----------------------------------------------------------------
  LTL properties
-----------------------------------------------------------------*)
CorrLtl ==
    [] ( ( \A p \in correct : pc[p] = "Init" )
         => <> ( \A p \in correct : pc[p] = "Accepted" ) )

RelayLtl ==
    [] ( ( \E p \in correct : pc[p] = "Accepted" )
         => <> ( \A p \in correct : pc[p] = "Accepted" ) )

UnforgLtl ==
    [] ( ( \A p \in correct : pc[p] = "NoInit" )
         => [] ( \A p \in correct : pc[p] # "Accepted" ) )

====