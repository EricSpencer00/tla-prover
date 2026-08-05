---- MODULE cbc_max ----
(* An encoding of the conditional consensus protocol based on the maximal value
   which is proposed by processes.  This protocol is described in Fig. 1 with
   condition C1 in [1]; the model and comments below are by Konnov, Tran and
   Widder, 2016.

   Mostéfaoui, Achour, et al. "Evaluating the condition-based approach to solve
   consensus." DSN 2003: Proceedings of the 2003 International Conference on
   Dependable Systems and Networks. IEEE, 2003.

   PATCHED (prove-TLA) -- a live TLC counterexample exposed two defects in the
   original encoding of the Receive action, both in the same line:
   (1) V was listed UNCHANGED on the same action line that let-bind V' from a
       message read, so the UNCHANGED silently overwrote the assignment (TLC:
       "changed while specified as UNCHANGED").
   (2) Even with (1 fixed, the model still had a bug: Receive marked ANY
       sent-but-not-yet-received message as received, and only recorded its value
       into V when pc[i] already matched the message's phase.  Otherwise the value
       was discarded via the ELSE branch, yet rcvdMsgs still counted the message
       as consumed: that message could never be received again, so it was
       permanently lost.  A message that legitimately arrives before its
       recipient reaches the matching phase (fully reachable under async
       interleaving) was therefore dropped, and later Phs1's MAX(V[i]) could CHOOSE
       from a row still carrying Bottom for that dropped vote.

   Both defects are corrected below: the phase/type match moves into the
   action's enabling guard, so Receive simply leaves a message untouched when the
   recipient is not yet in the matching phase -- it stays pending for the same
   recipient's own later Receive attempt, once pc[i] catches up.

   (3) A Quorum-decision check was encoded as a free disjunction, but in the
       source protocol (Mostefaoui-Rajsbaum-Raynal, JACM 50(6), Fig. 3, which DSN
       Fig. 1 instantiates with C1 / F = max) the quorum decision takes strict
       priority: it runs after every delivery and only when no value has a quorum
       among all N PHASE2 echoes can the deterministic fallback fire.  The free
       disjunction let a process ignore an available quorum and fall through to
       CHOOSE, deciding a different value than a quorum-decider.

   The fixes are a guarded phase match in Receive and a guarded CHOOSE
   disjunct in Phs2; neither weakens the protocol's correctness claims.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N
ASSUME \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs

vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>
Proc == 1..N
Status == { "BCAST1", "PHS1", "PREP", "BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

Msg1s  == [ type |-> "Phs1", value :> Values, sndr :> Proc ]
Msg2s  == [ type |-> "Phs2", value :> Values, wValue :> Values, sndr :> Proc ]
Msgs   == Msg1s \cup Msg2s
Phs1Msg(v_i, i) == [ type |-> "Phs1", value |-> v_i, sndr |-> i ]
Phs2Msg(v_i, w_i, i) == [ type |-> "Phs2", value |-> v_i, wValue |-> w_i, sndr |-> i ]

MAX(arr) == CHOOSE maxVal \in Values :
              /\ (\E p \in Proc: arr[p] = maxVal)
              /\ (\A p \in Proc: maxVal >= arr[p])

Init ==
  /\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc = [ i \in Proc |-> "BCAST1" ]
  /\ w = [ i \in Proc |-> Bottom ] /\ dval = [ i \in Proc |-> Bottom ]
  /\ nCrash = 0 /\ sntMsgs = {} /\ rcvdMsgs = [ i \in Proc |-> {} ]

(* Bounded crashes: a process becomes faulty only while fewer than F have. *)
Crash(i) ==
  /\ nCrash < F /\ pc[i] # "CRASH"
  /\ nCrash' = nCrash + 1 /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, v, w, dval, sntMsgs, rcvdMsgs >>

(* Receives ONE pending message that matches (pc[i] = its phase AND type). *)
Receive(i) ==
  \E msg \in Msgs :
    /\ pc[i] # "CRASH"
    /\ msg \in sntMsgs /\ msg \notin rcvdMsgs[i]
    /\ \/ /\ pc[i] = "PHS1" /\ msg.type = "Phs1"
         \/ /\ pc[i] = "PHS2" /\ msg.type = "Phs2"
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ V' = [ V EXCEPT ![i][msg.sndr] = msg.value ]
    /\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs >>

BcastPhs1(i) ==
  /\ pc[i] = "BCAST1" /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* Once at least N - F PHASE1s are in the view, the process estimates the
   maximum into w and moves to its own broadcast. *)
Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs1" }) >= N - T
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << V, v, dval, nCrash, sntMsgs, rcvdMsgs >>

BcastPhs2(i) ==
  /\ pc[i] = "BCAST2" /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* The majority decision fires only when the quorum-check (which runs after
   every delivery) never held; otherwise the deterministic fallback is
   unreachable.  No value can have two >= N - T quorums without > N senders. *)
Phs2(i) ==
  /\ pc[i] = "PHS2" /\ \/ \E v0 \in Values :
        /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) >= N - T
        /\ dval' = [ dval EXCEPT ![i] = v0 ] /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
        /\ UNCHANGED << v, w, nCrash, sntMsgs, rcvdMsgs, V >>
     \/ /\ \A j \in Proc: \E m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.sndr = j
        /\ \A v0 \in Values:
             Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << v, w, nCrash, sntMsgs, dval, rcvdMsgs, V >>

(* All PHASE2 messages are in the view; the process may deterministically
   pick any value it actually carried. *)
Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] = CHOOSE tV \in Values : (\E j \in Proc: tV = V[i][j]) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc :
          \/ Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
          \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)
          \/ /\ \A p \in Proc: pc[p] \in { "CRASH", "DONE" } /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in Proc: Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
                                 \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ Proc -> [ Proc -> { Bottom } \cup Values ] ]
  /\ v \in [ Proc -> Values ] /\ pc \in [ Proc -> Status ]
  /\ w \in [ Proc -> { Bottom } \cup Values ]
  /\ dval \in [ Proc -> { Bottom } \cup Values ]
  /\ nCrash \in 0 .. F /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

(* Every decision is some proposed value. *)
Validity == \A i \in Proc: (dval[i] # Bottom) => (\E j \in Proc: dval[i] = v[j])

(* Two processes never decide differently. *)
Agreement == \A i, j \in Proc: (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]

(* Every correct process eventually decides. *)
Termination == <>(\A i \in Proc: pc[i] \in { "CRASH", "DONE" })

(* At least F + 1 processes propose the greatest value MAX(v). *)
Condition1 == Cardinality({ j \in Proc: v[j] = MAX(v) }) > F

(* If Condition1 holds, the algorithm terminates. *)
RealTermination == Condition1 => Termination

====