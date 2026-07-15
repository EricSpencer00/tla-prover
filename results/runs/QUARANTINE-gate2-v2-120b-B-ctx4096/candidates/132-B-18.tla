---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The value domain *)
Value == {A, B, C}

(* Sequences of length up to 'bound' over Value *)
BoundedSeq(S) == 
  UNION { [i \in 1..n |-> s[i]] : n \in 0..bound, s \in [1..n -> S] }

VARIABLES seq, i, cand, cnt

(* Initial state: empty sequence, index i = 1, no candidate, zero count *)
Init ==
  /\ seq = << >>
  /\ i = 1
  /\ cand = Null
  /\ cnt = 0

(* Scanning the current element *)
Scan(i, cand, cnt) ==
  LET cur == seq[i] IN
  IF cnt = 0 THEN
    [cand |-> cur, cnt |-> 1]
  ELSE IF cand = cur THEN
    [cand |-> cand, cnt |-> cnt + 1]
  ELSE
    [cand |-> cand, cnt |-> cnt - 1]

(* Next-state relation *)
Next ==
  \/ /\ i <= Len(seq)                                    \* Scan step
     /\ let nxt == Scan(i, cand, cnt) in
        /\ cand' = nxt.cand
        /\ cnt'  = nxt.cnt
        /\ i'    = i + 1
        /\ UNCHANGED seq
  \/ /\ i > Len(seq)                                      \* After scan, optionally extend sequence
     /\ Len(seq) < bound
     /\ \E v \in Value :
          /\ cand' = v
          /\ cnt'  = 1
          /\ seq'  = Append(seq, v)
          /\ i'    = 1
  \/ /\ i > Len(seq) /\ Len(seq) = bound                 \* No further extension possible
     /\ UNCHANGED <<seq, i, cand, cnt>>

(* Specification *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* Safety property: the candidate is always an element of {A,B,C}
   (or Null before the first scan). *)
CandInValues == cand \in Value \/ cand = Null

=============================================================================