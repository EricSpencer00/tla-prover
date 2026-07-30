---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

Initializing == "initializing"
Idle == "idle"
Scanning == "scanning"
Finished == "finished"

VARIABLES seq, pos, candidate, count, phase
vars == << seq, pos, candidate, count, phase >>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ pos \in 0..Len(seq)
  /\ candidate \in Value \cup {Initializing}
  /\ count \in 0..Len(seq)
  /\ phase \in {Idle, Scanning, Finished}

OccurBefore(S, v) == { i \in 1..Len(seq) : seq[i] = v /\ i <= S }

Init ==
  /\ seq \in Seq(Value)
  /\ Len(seq) > 0
  /\ pos = 0
  /\ candidate = Initializing
  /\ count = 0
  /\ phase = Idle

Start ==
  /\ phase = Idle
  /\ phase' = Scanning
  /\ UNCHANGED << seq, pos, candidate, count >>

Scan ==
  /\ phase = Scanning
  /\ pos < Len(seq)
  /\ LET x == seq[pos + 1] IN
       IF candidate = Initializing
         THEN candidate' = x
            count' = 1
       ELSE IF candidate = x
         THEN candidate' = candidate
            count' = count + 1
       ELSE
         IF count > 1
           THEN candidate' = candidate
                count' = count - 1
           ELSE candidate' = Initializing
                count' = 0
  /\ pos' = pos + 1
  /\ UNCHANGED << seq, phase >>

Finish ==
  /\ phase = Scanning
  /\ pos = Len(seq)
  /\ phase' = Finished
  /\ UNCHANGED << seq, pos, candidate, count >>

Reset ==
  /\ phase = Finished
  /\ phase' = Idle
  /\ pos' = 0
  /\ candidate' = Initializing
  /\ count' = 0
  /\ UNCHANGED seq

Next == Start \/ Scan \/ Finish \/ Reset

Spec == Init /\ [][Next]_vars

Correct ==
  /\ phase = Finished
  /\ candidate # Initializing
  /\ (2 * Cardinality(OccurBefore(Len(seq), candidate))) > Len(seq)

Inv == TypeOK /\ Correct

====