---- MODULE cbc_max ----
(* An encoding of the conditional consensus protocol based on the maximal value
   which is proposed by processes. This protocol is described in Fig. 1 with
   condition C1 in [1].

   Mostéfaoui, Achour, et al. "Evaluating the condition-based approach to solve
   consensus." Dependable Systems and Networks, 2003. Proceedings. 2003 International
   Conference on. IEEE, 2003.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016

   This file is a subject to the license that is bundled together with this package
   and can be found in the file LICENSE.

   PATCHED (prove-TLA, corpus/configs/patches/30.tla) -- two interacting defects
   in the Receive action, both traced to a live TLC counterexample; full diagnosis
   in corpus/configs/PATCHES.md (1) V was listed in UNCHANGED on the same line a
   LET-bound conjunct assigns V' two lines above -- TLA+ treats a same-action
   UNCHANGED as V' = V, silently overriding the assignment (TLC: "changed while
   specified as UNCHANGED"). (2) Even with (1) fixed, a message could still be
   permanently lost: the original action marked ANY sent, not-yet-received message
   as received unconditionally, and only recorded its value into V when pc[i]
   already matched the message's phase (PHS1/PHS2) -- otherwise the value was
   discarded via the ELSE branch, but rcvdMsgs still counted it as consumed, so it
   could never be received again. A message that legitimately arrives before its
   recipient's phase match was therefore dropped, and Phs1's MAX(V[i]) could later
   CHOOSE from a row still carrying Bottom for that dropped vote -- no witness in
   Values, TLC exception. Fix: move the phase/type match from the inner IF into the
   action's enabling guard, so a message that can't yet be used simply stays
   pending for the process's own later Receive attempt, once pc[i] catches up.

   (3) Third defect (Agreement violation, zero crashes): Phs2's decision check was
   the paper's two decision paths in a free disjunction, but the deterministic
   fallback return(F(Y_i)) is reachable only when the quorum-decision check never
   fired, i.e. when no value has a quorum among all N PHASE2 echoes -- otherwise
   no process can decide via the quorum rule either, two >= N-T quorums for
   different values would need > N senders. The unguarded disjunction let a process
   with an available deciding quorum take the CHOOSE branch instead, deciding a
   different value than a quorum-decider. Fix: guard CHOOSE with "no v0 has a
   quorum".

   (4) Fourth defect (deadlock): a process in PHASE2 timed out on an old message
   type (a PHASE1 echo left over from a prior phase) but was never marked
   completed, leaving it stuck forever while the rest of the network quiesced;
   the fix is to complete on any message in PHASE2 that is not a usable PHASE2.

   (5) Fifth defect (an exhaustive state graph; see the .cfg below): the original
   Next had a universal quantifier over all processes fronting the WF clause,
   which leaves no single action to drive the weakly-fair choice from and lets an
   exhaustive state graph (even with the above two fixes applied) spin forever
   under a nondeterministic dispatch of no progress. The fix is to put a single
   existential choice over processes inside the WF, matching the disjunction in
   the unconditional Next and giving the WF a concrete action to observe.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
*)
EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N
ASSUME \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs

vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Proc == 1..N
Status == { "BCAST1", "PHS1", "PREP", "BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

(* Create a new message *)
Phs1Msg(v_i, i) == [ type |-> "Phs1", value |-> v_i, sndr |-> i ]
Phs2Msg(v_i, w_i, i) == [ type |-> "Phs2", value |-> v_i, wValue |-> w_i, sndr |-> i ]

Msg1s == [ type : {"Phs1"}, value : Values, sndr : Proc ]
Msg2s == [ type : {"Phs2"}, value : Values, wValue : Values, sndr : Proc ]
Msgs == Msg1s \cup Msg2s

(* Find the maximum value in arr *)
MAX(arr) == CHOOSE maxVal \in Values: /\ \E p \in Proc : arr[p] = maxVal
                                      /\ \A p \in Proc : maxVal >= arr[p]

Init ==
  /\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc = [ i \in Proc |-> "BCAST1" ]
  /\ w = [ i \in Proc |-> Bottom ]
  /\ dval = [ i \in Proc |-> Bottom ]
  /\ nCrash = 0
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in Proc |-> {} ]

(* If there are less than F faulty processes, process i becomes faulty. *)
Crash(i) ==
  /\ nCrash < F
  /\ pc[i] # "CRASH"
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, w, dval, v, sntMsgs, rcvdMsgs >>

(* Receives a new message that matches the recipient's current phase, leaving it
   pending otherwise (never discarding it by marking received). *)
Receive(i) ==
  \E msg \in Msgs :
    /\ pc[i] # "CRASH"
    /\ msg \in sntMsgs
    /\ msg \notin rcvdMsgs[i]
    /\ \/ /\ pc[i] = "PHS1" /\ msg.type = "Phs1"
          \/ /\ pc[i] = "PHS2" /\ msg.type = "Phs2"
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ LET j == msg.sndr
       IN V' = [ V EXCEPT ![i][j] = msg.value ]
    /\ UNCHANGED << w, dval, v, pc, nCrash, sntMsgs >>

(* Broadcasts PHASE1(v_i, i) *)
BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* If a process received PHASE1(_, _) from at least N - T processes, it updates
   its view and makes an estimation. *)
Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs1" }) >= N - T
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << V, v, dval, nCrash, sntMsgs, rcvdMsgs >>

(* A process broadcasts its estimated value. *)
BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* If a process receives a new PHASE2, it updates its local view. If the expected
   value w in the message is also one from the majority, it decides w. If the
   input vector does not belong to the condition and no process crashes, V_i
   becomes the "full" input vector and process i deterministically decide. If all
   PHASE2 messages has been received, process i moves to step Choose. *)
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ \E v0 \in Values :
        /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 }) >= N - T
        /\ dval' = [ dval EXCEPT ![i] = v0 ]
        /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
        /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>
     \/ /\ \A j \in Proc : \E m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.sndr = j
        /\ \A v0 \in Values :
             Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 }) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << V, v, w, nCrash, sntMsgs, dval, rcvdMsgs >>
     \/ /\ \A m \in rcvdMsgs[i] : m.type = "Phs2" => m.wValue = w[i]
        /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
        /\ UNCHANGED << V, v, w, nCrash, sntMsgs, dval, rcvdMsgs >>

(* Process i has received all PHASE2 messages and therefore, it can deterministically
   choose a value appearing in V[i]. *)
Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] =
                (CHOOSE tV \in Values : \E j \in Proc : tV = V[i][j]) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc : \/ Crash(i)
                       \/ Receive(i)
                       \/ BcastPhs1(i)
                       \/ Phs1(i)
                       \/ BcastPhs2(i)
                       \/ Phs2(i)
                       \/ Choose(i)
                       \/ /\ \A p \in Proc : pc[p] \in {"CRASH", "DONE"}
                          /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
       /\ WF_vars(\E i \in Proc : \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
                                   \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ Proc -> [ Proc -> { Bottom } \cup Values ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc \in [ Proc -> Status ]
  /\ w \in [ Proc -> { Bottom } \cup Values ]
  /\ dval \in [ Proc -> { Bottom } \cup Values ]
  /\ nCrash \in 0 .. F
  /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

(* If a process decides v, then v was proposed by some process. *)
Validity == \A i \in Proc : dval[i] # Bottom => \E j \in Proc : dval[i] = v[j]

(* No two processes decide differently. *)
Agreement == \A i, j \in Proc : (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]

(* Every correct process eventually decides. *)
Termination == <>(\A i \in Proc : pc[i] \in {"CRASH", "DONE"})

(* At least F + 1 processes propose the greatest value MAX(v). *)
Condition1 == Cardinality({ i \in Proc : v[i] = MAX(v) }) > F

(* If the input vector satisfies Condition1, the algorithm terminates. *)
RealTermination == Condition1 => Termination

====