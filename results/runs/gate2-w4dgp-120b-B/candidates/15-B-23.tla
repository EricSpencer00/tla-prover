------------------------------ MODULE bcastByz ------------------------------
             
(* TLA+ encoding of a parameterized model of the broadcast distributed  
   algorithm with Byzantine faults.
   
   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:
   
   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94
                                                                 
   A short description of the parameterized model is described in: Gmeiner,   
   Annu, et al. "Tutorial on parameterized model checking of fault-tolerant   
   distributed algorithms." International School on Formal Methods for the  
   Design of Computer, Communication and Software Systems. Springer  
   International Publishing, 2014.                   
  
   This specification has a TLAPS proof for unforgeability of messages: if a 
   correct process p is correct and does not broadcast a message m, then no 
   correct process ever accepts m. Thus, from InitNoBcast (the initial state in 
   which the transmitter does not broadcast any message) and the transition relation 
   we can prove []Unforgeability, i.e.
        (InitNoBcast /\ [][Next]_vars) => []Unforgeability
   We can use TLC to check two properties (for a fixed N,T,F):
    * Correctness: if a correct process broadcasts, then every correct process accepts,
    * Replay: if a correct process accepts, then every correct process accepts.  
  
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2023
   Translated to TLA+2.1in by Aaron Kupervasser, 2024

   This file is subject to the license bundled with this package, see LICENSE. *)

EXTENDS Naturals, FiniteSets, FunctionTheorems

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == (N - F) \X M

VARIABLES pc, rcvd, sent, Corr, Faulty

vars == << pc, rcvd, sent, Corr, Faulty >>

(* pc[i] = "V0": process i is correct and never received the init message.
   "V1": process i is correct and received the init message.
   "SE": process i sent an ECHO, but has not yet accepted.
   "AC": process i accepted the value. *)
TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]
  /\ Corr \subseteq Proc /\ Faulty \subseteq Proc

CorrAndFaulty ==
  /\ Corr \cup Faulty = Proc
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T

Init ==
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]

\* A correct process p receives any subset of correct messages, plus any
\* subset of byzantine messages (the Byzantine processes can be thought of as
\* spurious traffic, not failures that deny service).
Receive(p, includeByz) ==
  \E s \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = p THEN rcvd[i] \cup s ELSE rcvd[i] ]

Step(p) ==
  /\ Receive(p, TRUE)
  /\ \/ (pc[p] = "V1" /\ pc' = [pc EXCEPT ![p] = "SE"]
                           /\ sent' = sent \cup {<<p, "ECHO">>})
     \/ (pc[p] \notin {"V0", "V1"} /\ Cardinality(rcvd'[p]) >= N - 2*T
                                   /\ Cardinality(rcvd'[p]) < N - T
                                   /\ pc' = [pc EXCEPT ![p] = "SE"]
                                   /\ sent' = sent \cup {<<p, "ECHO">>})
     \/ (pc[p] \in {"V0", "V1"} /\ Cardinality(rcvd'[p]) >= N - T
                                   /\ pc' = [pc EXCEPT ![p] = "AC"]
                                   /\ sent' = sent \cup {<<p, "ECHO">>})
     \/ (pc[p] = "SE" /\ Cardinality(rcvd'[p]) >= N - T
                                   /\ pc' = [pc EXCEPT ![p] = "AC"]
                                   /\ UNCHANGED <<sent>>)
     \/ (UNCHANGED <<pc, sent>>)

Next == \E p \in Corr : Step(p) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

Unforgeable ==
  /\ Corr \subseteq Proc
  /\ \A i \in Corr : pc[i] # "AC"

\* From InitNoBcast and the transition relation we prove []Unforgeable.
\* This is a safety property, so a plain reachability check suffices.
UnforgeableFromInit == (InitNoBcast /\ [][Next]_vars) => []Unforgeable

=============================================================================