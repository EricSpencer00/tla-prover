---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets
CONSTANTS Value

ASSUME Value # {}

VARIABLES candidate, count, seq, pos, walked, occ
vars == <<candidate, count, seq, pos, walked, occ>>

Init ==
  /\ candidate \in Value
  /\ count \in 0..3
  /\ seq = << >>
  /\ pos = 0
  /\ walked = 0
  /\ occ = [v \in Value |-> {}]

AddSeq ==
  /\ walked < 3
  /\ \E x \in Value :
       seq' = Append(seq, x)
  /\ walked' = walked + 1
  /\ UNCHANGED <<candidate, count, pos, occ>>

VoterScan ==
  /\ count = 0
  /\ candidate' = seq[pos]
  /\ count' = 1
  /\ occ' = [occ EXCEPT ![seq[pos]] = @ \cup {pos}]
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq, walked>>

VoterCancel ==
  /\ count > 0
  /\ candidate # seq[pos]
  /\ count' = count - 1
  /\ pos' = pos + 1
  /\ UNCHANGED <<candidate, seq, walked, occ>>

VoterWin ==
  /\ count > 0
  /\ candidate = seq[pos]
  /\ count' = count + 1
  /\ occ' = [occ EXCEPT ![seq[pos]] = @ \cup {pos}]
  /\ pos' = pos + 1
  /\ UNCHANGED <<candidate, seq, walked>>

Recover ==
  /\ count = 0
  /\ \E v \in Value :
       occ' = [occ EXCEPT ![v] = {}]
  /\ UNCHANGED <<candidate, count, seq, pos, walked>>

Next == AddSeq \/ VoterScan \/ VoterCancel \/ VoterWin \/ Recover

Spec == Init /\ [][Next]_vars

TypeOK == /\ candidate \in Value
          /\ count \in 0..3
          /\ seq \in Seq(Value)
          /\ pos \in 0..3
          /\ walked \in 0..3
          /\ occ \in [Value -> SUBSET 0..2]

Inv == (pos = 3) => (cardinality(occ[candidate]) * 2 > walked /\ walked >= 1)

Correct == (pos = 3) => (walked >= 1 => (cardinality(occ[candidate]) * 2 > walked))

====