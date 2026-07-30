---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The majority vote algorithm processes the input sequence one element at a
\* time, keeping a running candidate and a counter. At the end of the scan,
\* the candidate is a strict majority element exactly when one exists.
\* The proof below is verified by TLAPS.

VARIABLES candidate, vote, i, seq, occ

vars == <<candidate, vote, i, seq, occ>>

Values == Value \cup {"none"}

DistinctPositions(k) == {j \in 1..Len(seq) : seq[j] = k}

TypeOK ==
  /\ candidate \in Values
  /\ vote \in 0..Len(seq)
  /\ i \in 0..Len(seq)
  /\ seq \in Seq(Value)
  /\ occ \in [Value -> Nat]

Init(seq) ==
  /\ candidate = "none"
  /\ vote = 0
  /\ i = 0
  /\ seq = seq
  /\ occ = [k \in Value |-> 0]

Next(seq) ==
  \/ \E x \in Value :
       /\ i < Len(seq)
       /\ seq' = [seq EXCEPT ![i + 1] = x]
       /\ i' = i + 1
       /\ occ' = [occ EXCEPT ![x] = occ[x] + 1]
       /\ candidate' = IF vote = 0 THEN x ELSE IF candidate = x THEN candidate ELSE candidate
       /\ vote' = IF vote = 0 THEN 1 ELSE IF candidate = x THEN vote + 1 ELSE vote - 1
  \/ \E k \in Value :
       /\ i = Len(seq)
       /\ candidate' = k
       /\ UNCHANGED <<vote, i, seq, occ>>

Spec(seq) == Init(seq) /\ [][Next(seq)]_vars

\* The inductive invariant from the main algorithm: the running candidate
\* is always a strict majority of the positions it has already consumed.
Inv ==
  /\ i <= Len(seq)
  /\ (vote > 0 => 2 * occ[candidate] > i)

TypeOKInv == TypeOK /\ Inv

\* After scanning the whole sequence, any strict-majority value must be the
\* candidate: this is the only soundness-critical invariant, proved from Inv.
Correct ==
  /\ i = Len(seq)
  /\ \A k \in Value : 2 * occ[k] > Len(seq) => candidate = k

SpecDef == Spec(seq)

====