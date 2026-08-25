---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

IndexSet(I) == I[1] .. I[2]

CountInSeq(s, x) ==
  Cardinality({ i \in 1..Len(s) : s[i] = x })

CountInInterval(s, I, x) ==
  Cardinality({ i \in IndexSet(I) : s[i] = x })

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Permutation(s, t) ==
  \A x \in Values : CountInSeq(s, x) = CountInSeq(t, x)

LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= MaxSeqLen }

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc   = "Loop"

(* ---------------------------------------------------------------------- *)
(* Partition operator (abstract) *)

Partition(s0, I, p) ==
  { s \in LimitedSeq(Values) :
      /\ Len(s) = Len(s0)
      /\ \A i \in 1..Len(s0) :
           IF i \notin IndexSet(I) THEN s[i] = s0[i] ELSE TRUE
      /\ \A x \in Values :
           CountInInterval(s, I, x) = CountInInterval(s0, I, x)
      /\ \A i \in IndexSet(<<I[1], p>>):
           \A j \in IndexSet(<<p+1, I[2]>>):
               s[i] <= s[j] }

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E I \in work :
          /\ I[1] <= I[2]
          /\ IF I[1] = I[2] THEN
               /\ work' = work \ {I}
               /\ seq'  = seq
               /\ orig' = orig
               /\ pc'   = "Loop"
             ELSE
               /\ \E p \in IndexSet(I) :
                    /\ \E s \in Partition(seq, I, p) :
                         /\ seq'  = s
                         /\ orig' = orig
                         /\ work' = (work \ {I})
                                   \cup (IF I[1] <= p   THEN {<<I[1], p>>}    ELSE {})
                                   \cup (IF p+1 <= I[2] THEN {<<p+1, I[2]>>} ELSE {})
                         /\ pc'   = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc'   = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
  /\ seq  \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq { <<i,j>> : i \in 1..Len(seq), j \in i..Len(seq) }
  /\ pc \in {"Loop", "Done"}

PCorrect == (pc = "Done") <=> (work = {})

Inv ==
  /\ Permutation(seq, orig)
  /\ (work = {} => Sorted(seq))

(* ---------------------------------------------------------------------- *)
(* Property *)

Termination == <> (work = {})

====