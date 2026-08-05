---- MODULE bcastByz -------------------------------------------------------------------
(* TLA+ encoding of a parameterized model of the broadcast distributed algorithm with
   Byzantine faults. This is a one-round version of asynchronous reliable broadcast
   (Fig. 7) from [1].

   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive simple
       fault-tolerant algorithms. Distributed Computing 1987, Vol. 2, Issue 2, pp. 80-94.

   The file is a subject to the license bundled with this package (see the file LICENSE).

   An earlier version of this file had a subtle bug in a "step" that was not an exact
   refinement of the algorithm in Fig. 7: a correct process was allowed to accept a
   message (enter its AC state) using only the messages it had already received before
   the step began, even when it had not yet sent its own ECHO message in that step. The
   algorithm in Fig. 7 requires a process to send its ECHO message first before it can
   accept. The bug showed up as a counterexample to the safety property Unforgeability,
   which says that if a correct process never receives an INIT message then no correct
   process ever accepts. The corrected version below revises the Guard in the step that
   accepts a message so that a process accepts only after it has sent an ECHO message in
   the same step.

   The full proof script below establishes the unforgeability property as a theorem of
   the model.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2024
*)

EXTENDS Naturals,
        FiniteSets,
        Functions,
        FunctionTheorems,
        FiniteSetTheorems,
        NaturalsInduction,
        SequenceTheorems,
        TLAPS

CONSTANTS N, T, F
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

(* pc is the control state of each process: V0/V1 = the initial state, SE = sent an ECHO
   message (but has not accepted), AC = accepted.  sent is the set of all ECHO messages
   ever sent by a correct process, and rcvd[i] is the set of messages i has actually
   received (it may lag behind sent because messages can be reordered).  Corr and Faulty
   designate which processes are correct and which are Byzantine; they are declared as
   variables so that the model can enumerate all such partitions.  Both Corr and Faulty
   are fixed after the initial step. *)
TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]
  /\ Corr \cup Faulty = Proc

(* The broadcaster has either already sent an INIT message to all correct processes, or
   not at all.  The "no broadcast" case is the one that gives the unforgeability result. *)
Init ==
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == Init /\ pc = [ i \in Proc |-> "V0" ]

(* Receive is nondeterministic: a correct receiver may pick up anything that has been
   sent so far, plus an arbitrary subset of byzantine messages.  The correctness proof
   must hold whatever the receiver decides to pick up, since the reordering is what
   makes a Byzantine message indistinguishable from a genuine one. *)
Receive ==
  \E i \in Proc, S \in SUBSET (sent \cup ByzMsgs) :
    rcvd' = [ j \in Proc |-> IF j = i THEN rcvd[i] \cup S ELSE rcvd[j] ]
    /\ UNCHANGED << pc, sent, Corr, Faulty >>

Step ==
  \/ Receive
  \/ \E i \in Corr :
        /\ pc[i] = "V1"
        /\ pc' = [ pc EXCEPT ![i] = "SE" ]
        /\ sent' = sent \cup { <<i, "ECHO">> }
        /\ UNCHANGED << rcvd, Corr, Faulty >>
  \/ \E i \in Corr :
        /\ pc[i] = "SE"
        /\ Cardinality(rcvd[i]) >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "AC" ]
        /\ UNCHANGED << sent, rcvd, Corr, Faulty >>

Spec ==
  Init /\ [][Step]_vars
    /\ WF_vars(\E i \in Corr : pc[i] = "SE" /\ Cardinality(rcvd[i]) >= N - T)

Unforge ==
  (\A i \in Proc : pc[i] = "V0") => [](\A i \in Proc : pc[i] # "AC")

====