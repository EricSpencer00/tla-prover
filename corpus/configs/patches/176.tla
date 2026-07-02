------------------------------ MODULE spanning ------------------------------
EXTENDS Integers
CONSTANTS Proc, NoPrnt, root, nbrs
ASSUME NoPrnt \notin Proc /\ nbrs \subseteq Proc \times Proc
VARIABLES prnt, rpt, msg
vars == <<prnt, rpt, msg>>

Init == /\ prnt = [i \in Proc |-> NoPrnt]
        /\ rpt = [i \in Proc |-> FALSE]
        /\ msg = {}

CanSend(i, j) ==  (<<i, j>> \in nbrs) /\ (i = root \/ prnt[i] # NoPrnt)

Update(i, j) == /\ prnt' = [prnt EXCEPT ![i] = j]
                /\ UNCHANGED <<rpt, msg>>

Send(i) == \E k \in Proc: /\ CanSend(i, k) /\ (<<i, k>> \notin msg)
                          /\ msg' = msg \cup {<<i, k>>}
                          /\ UNCHANGED <<prnt, rpt>>

Parent(i) == /\ prnt[i] # NoPrnt /\ ~rpt[i]
             /\ rpt' = [rpt EXCEPT ![i] = TRUE]
             /\ UNCHANGED <<msg, prnt>>

Next == \E i, j \in Proc: IF i # root /\ prnt[i] = NoPrnt /\ <<j, i>> \in msg
                          THEN Update(i, j)
                          ELSE \/ Send(i) \/ Parent(i)
                               \/ UNCHANGED <<prnt, msg, rpt>>

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(\E i, j \in Proc: IF i # root /\ prnt[i] = NoPrnt /\ <<j, i>> \in msg
                                     THEN Update(i, j)
                                     ELSE \/ Send(i) \/ Parent(i)
                                          \/ UNCHANGED <<prnt, msg, rpt>>)

(* PATCHED (prove-TLA, corpus/configs/patches/176.tla): TypeOK (and Termination,
   same pattern) checked "<<i, prnt[i]>> \in nbrs" -- the edge FROM the child i TO
   its parent. But CanSend(i,j) == <<i,j>> \in nbrs /\ ... defines nbrs as the
   direction a process SENDS in, and only the root/already-connected processes
   send (CanSend's second conjunct) -- so edges run PARENT -> CHILD, never the
   reverse. With MC_spanning's Neighbors == {<<1,2>>,<<1,3>>} (root 1 -> children
   2,3), the algorithm correctly sets prnt[2]=1 after child 2 receives root's
   message, but TypeOK then asks whether <<2,1>> \in nbrs -- the reverse edge,
   which was never in nbrs to begin with. Live TLC counterexample at
   results/runs/oracle-v1/logs/175.log, State 3: prnt=<<NoPrnt,1,NoPrnt>>,
   TypeOK fails on i=2 checking <<2,1>> against nbrs={<<1,2>>,<<1,3>>}. Byte-
   identical to upstream (tlaplus/examples specifications/spanning/spanning.tla),
   confirmed via diff -- never caught there either. Fix: check the edge in the
   direction it's actually defined, <<prnt[i], i>> \in nbrs, in both TypeOK and
   Termination. See corpus/configs/PATCHES.md. *)
TypeOK == /\ \A i \in Proc : prnt[i] = NoPrnt \/ <<prnt[i], i>> \in nbrs
          /\ rpt \in [Proc -> BOOLEAN]
          /\ msg \subseteq Proc \times Proc

Termination == <>(\A i \in Proc : i = root \/ (prnt[i] # NoPrnt /\ <<prnt[i], i>> \in nbrs))

OneParent == [][\A i \in Proc : prnt[i] # NoPrnt => prnt[i] = prnt'[i]]_vars

SntMsg == \A i \in Proc: (i # root /\ prnt[i] = NoPrnt => \A j \in Proc: <<i ,j>> \notin msg)

=============================================================================
\* Modification History
\* Last modified Mon Jul 09 13:30:26 CEST 2018 by tthai
