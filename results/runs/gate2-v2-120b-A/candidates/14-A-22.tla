---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat, Nat

\* Finite domination of Nat:
Nat == 0 .. MaxNat

VARIABLES pc, tn, lp, k

(*--algorithm Boulanger
variables pc = [i \in 1..N |-> "idle"];
          tn = [i \in 1..N |-> 0];
          lp = 0;
          k  = 0;

define
  ProcSet == 1..N;
  TicketLessOrEqual(i, j) ==
    /\ tn[i] < tn[j]
    \/ /\ tn[i] = tn[j]
       /\ i <= j;
end define;

process (i \in ProcSet)
variables myt;
begin
  while TRUE do
    await pc[i] = "idle";
    pc[i] := "wait1";
    pc[i] := "wait2";
    tn[i] := k;
    lp := i;
    while /\ pc[i] = "wait2"
          /\ \E j \in ProcSet :
                j /= i /\ tn[j] # 0 /\ tn[j] < tn[i] /\ pc[j] # "cs" do
      skip;
    end while;
    pc[i] := "cs";
    pc[i] := "idle";
    tn[i] := 0;
    k := IF k = MaxNat - 1 THEN 0 ELSE k + 1;
  end while;
end process;
end algorithm Boulanger *)

\* The above algorithm is for illustration.  The actual TLA+ model reuses its
\* actions directly.

\* Initial predicate (mirrors the algorithm's start state)
Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ tn = [i \in 1..N |-> 0]
  /\ lp = 0
  /\ k  = 0

\* Step actions (expressed directly as they appear in the algorithm)
\* 1. Begin request
BeginReq(i) ==
  /\ i \in 1..N
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "wait1"]
  /\ tn' = tn
  /\ lp' = lp
  /\ k'  = k

\* 2. Take ticket
TakeTicket(i) ==
  /\ i \in 1..N
  /\ pc[i] = "wait1"
  /\ tn[i] \in Nat
  /\ pc' = [pc EXCEPT ![i] = "wait2"]
  /\ tn' = [tn EXCEPT ![i] = k]
  /\ lp' = i
  /\ k'  = IF k = MaxNat - 1 THEN 0 ELSE k + 1

\* 3. Wait until safe
Wait(i) ==
  /\ i \in 1..N
  /\ pc[i] = "wait2"
  /\ \E j \in 1..N :
        j # i /\ tn[j] # 0 /\ tn[j] < tn[i] /\ pc[j] = "cs"
  /\ pc' = pc
  /\ tn' = tn
  /\ lp' = lp
  /\ k'  = k

\* 4. Enter critical section
EnterCS(i) ==
  /\ i \in 1..N
  /\ pc[i] = "wait2"
  /\ \A j \in 1..N :
        j # i => tn[j] = 0 \/ tn[j] > tn[i] \/ pc[j] # "cs"
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ tn' = tn
  /\ lp' = lp
  /\ k'  = k

\* 5. Exit critical section
ExitCS(i) ==
  /\ i \in 1..N
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ tn' = [tn EXCEPT ![i] = 0]
  /\ lp' = lp
  /\ k'  = k

\* Next-state relation
Next ==
  \/ \E i \in 1..N : BeginReq(i)
  \/ \E i \in 1..N : TakeTicket(i)
  \/ \E i \in 1..N : Wait(i)
  \/ \E i \in 1..N : EnterCS(i)
  \/ \E i \in 1..N : ExitCS(i)

\* Full behavior specification
Spec == Init /\ [][Next]_<<pc, tn, lp, k>>

\* Safety invariants
MutualExclusion ==
  \A i, j \in 1..N :
    (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
  /\ pc \in [1..N -> {"idle", "wait1", "wait2", "cs"}]
  /\ tn \in [1..N -> Nat]
  /\ lp \in 0..N
  /\ k  \in Nat

Inv ==
  /\ MutualExclusion
  /\ TypeOK

\* State constraint to keep ticket numbers below MaxNat
StateConstraint ==
  \A i \in 1..N : tn[i] < MaxNat

\* The model checker will apply the constraint automatically

\* The required identifiers for the .cfg file
SPECIFICATION Spec
INVARIANT Inv
INVARIANT MutualExclusion
INVARIANT TypeOK

====