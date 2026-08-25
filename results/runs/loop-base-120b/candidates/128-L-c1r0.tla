---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Count(seq, val) == 
  Cardinality({ i \in 1..Len(seq) : seq[i] = val })

Permutes(s1, s2) == 
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values : Count(s1, v) = Count(s2, v)

Intervals(seq) == 
  { <<i, j>> : i \in 1..Len(seq), j \in i..Len(seq) }

Sorted(seq) == 
  \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

Partition(seq, int, p) == 
  LET low == int[1] 
      high == int[2] 
  IN 
    { seq2 \in LimitedSeq(Values) :
        /\ Len(seq2) = Len(seq)
        /\ \A k \in 1..Len(seq) :
             IF k \notin low..high THEN seq2[k] = seq[k] ELSE TRUE
        /\ \A j \in low..p :
               \A k \in p..high :
                 seq2[j] <= seq2[p] /\ seq2[p] <= seq2[k]
        /\ Permutes( seq[low..high] , seq2[low..high] )
    }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
  /\ seq \in LimitedSeq(Values) 
  /\ Len(seq) >= 1
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == 
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E int \in work :
          LET low  == int[1] 
              high == int[2] 
          IN 
            IF low = high THEN
              /\ seq' = seq
              /\ orig' = orig
              /\ work' = work \ {int}
              /\ pc'   = "Loop"
            ELSE
              /\ \E p \in low..high :
                    LET lower == IF low <= p-1 THEN { <<low, p-1>> } ELSE {}
                        upper == IF p+1 <= high THEN { <<p+1, high>> } ELSE {}
                    IN 
                      /\ \E seq2 \in Partition(seq, int, p) :
                            /\ seq' = seq2
                            /\ orig' = orig
                      /\ work' = (work \ {int}) \cup lower \cup upper
                      /\ pc'   = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK == 
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq Intervals(seq)
  /\ pc \in {"Loop", "Done"}

Inv == 
  /\ Permutes(seq, orig)
  /\ \A int \in work : int[1] <= int[2]

PCorrect == 
  pc = "Done" => 
    /\ Sorted(seq)
    /\ Permutes(seq, orig)

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====