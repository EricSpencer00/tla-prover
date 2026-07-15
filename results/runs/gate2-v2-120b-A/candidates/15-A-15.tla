---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N, T, F

VARIABLES correct, faulty, pc, msgs, sent

(*--algorithm bcastByz
variables correct, faulty, pc, msgs, sent;
begin
  \* initialization is defined in Init below
end algorithm;*)

(* ------------------------------------------------------------------------ *)
(*  Enumerated values for program counters                                    *)
(* ------------------------------------------------------------------------ *)
PcVals == {"Init", "NoInit", "Echo", "Accept"}

(* ------------------------------------------------------------------------ *)
(*  Message definition                                                        *)
(* ------------------------------------------------------------------------ *)
Msg == {"ECHO"}

(* ------------------------------------------------------------------------ *)
(*  Initial state definition                                                 *)
(* ------------------------------------------------------------------------ *)
Init ==
  /\ correct \subseteq 1..N
  /\ |\{ correct \}| = N - F
  /\ faulty = (1..N) \ correct
  /\ pc = [i \in 1..N |-> 
            IF i \in correct 
               THEN IF i \in correct \ {1}  \* nondet choice for who gets INIT
                       THEN "Init"
                       ELSE "NoInit"
               ELSE "NoInit"]
  /\ msgs = [i \in 1..N |-> {}]
  /\ sent = {}

(* ------------------------------------------------------------------------ *)
(*  Helper functions                                                         *)
(* ------------------------------------------------------------------------ *)

ReceivedEchoes(i) == { m \in msgs[i] : m = "ECHO" }

DistinctEchoSenders(i) ==
  { j \in 1..N : "ECHO" \in msgs[i] /\ j \in sent }

CanSendEcho(i) == 
  /\ i \notin sent
  /\ ( (pc[i] = "Init") => TRUE
       /\ (pc[i] = "NoInit") => 
            /\ Cardinality(DistinctEchoSenders(i)) >= N - 2*T
         )
     )

SendEcho(i) ==
  /\ sent' = sent \cup {i}
  /\ msgs' = [msgs EXCEPT ![j] = IF i \in correct THEN msgs[j] \cup {"ECHO"} ELSE msgs[j] 
                                             \* faulty may also send arbitrary ECHO, modelled nondet *)
  /\ UNCHANGED <<correct, faulty, pc>>

Accept(i) == 
  /\ pc' = [pc EXCEPT ![i] = "Accept"]
  /\ UNCHANGED <<correct, faulty, msgs, sent>>

(* ------------------------------------------------------------------------ *)
(*  Next-state relation                                                      *)
(* ------------------------------------------------------------------------ *)
Next ==
  \/ \E i \in correct :
        /\ pc[i] = "Init"
        /\ Accept(i)
  \/ \E i \in correct :
        /\ pc[i] = "NoInit"
        /\ Cardinality(DistinctEchoSenders(i)) >= N - T
        /\ SendEcho(i)
        /\ Accept(i)
  \/ \E i \in correct :
        /\ pc[i] = "NoInit"
        /\ Cardinality(DistinctEchoSenders(i)) >= N - 2*T
        /\ Cardinality(DistinctEchoSenders(i)) < N - T
        /\ SendEcho(i)
  \/ \E i \in correct :
        /\ pc[i] = "Echo"
        /\ Cardinality(DistinctEchoSenders(i)) >= N - T
        /\ Accept(i)
  \/ \E i \in correct :
        /\ pc[i] = "Init"
        /\ SendEcho(i)
  \/ \E i \in correct :
        /\ pc[i] = "NoInit"
        /\ Cardinality(DistinctEchoSenders(i)) >= N - 2*T
        /\ Cardinality(DistinctEchoSenders(i)) < N - T
        /\ SendEcho(i)
  \/ \E i \in correct :
        /\ pc[i] = "Echo"
        /\ Cardinality(DistinctEchoSenders(i)) >= N - T
        /\ Accept(i)

Spec == Init /\ [][Next]_<<correct, faulty, pc, msgs, sent>>

(* ------------------------------------------------------------------------ *)
(*  Safety invariants                                                        *)
(* ------------------------------------------------------------------------ *)
TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> PcVals]
  /\ msgs \in [1..N -> SUBSET Msg]
  /\ sent \subseteq 1..N

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* ------------------------------------------------------------------------ *)
(*  Liveness properties (expressed as temporal formulas)                    *)
(* ------------------------------------------------------------------------ *)

CorrLtl == 
  /\ \A i \in correct : pc[i] = "Init" 
  => <> ( \A j \in correct : pc[j] = "Accept" )

RelayLtl ==
  /\ \E i \in correct : pc[i] = "Accept"
  => <> ( \A j \in correct : pc[j] = "Accept" )

UnforgLtl ==
  /\ \A i \in correct : pc[i] = "NoInit"
  => [] ( \A j \in correct : pc[j] # "Accept" )

=============================================================================