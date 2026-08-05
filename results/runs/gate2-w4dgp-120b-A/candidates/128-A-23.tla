---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The partition operator abstracts the Quicksort partition step: for a chosen
\* interval and pivot it names exactly the set of sequences that could result
\* from a correct partition of the current sequence, leaving everything outside
\* the interval untouched, and never inventing or dropping an element.
Partition(sq, lo, hi, p) ==
  { s \in [DOMAIN sq -> Values] :
        /\ \A i \in DOMAIN sq :
             (i < lo \/ i > hi) => s[i] = sq[i]
        /\ \A i \in lo..hi : s[i] \in Values
        /\ \A i \in lo..p, j \in (p+1)..hi : s[i] <= s[j]
        /\ \A x \in Values : \E i \in DOMAIN sq : sq[i] = x => \E j \in DOMAIN sq : s[j] = x
      }

VARIABLES seq, original, todo, pc
vars == <<seq, original, todo, pc>>

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ original \in [1..MaxSeqLen -> Values]
  /\ todo \in SUBSET (SUBSET (1..MaxSeqLen))

PCorrect ==
  pc = "done" => /\ \A i, j \in DOMAIN seq : i < j => seq[i] <= seq[j]
                  /\ \A x \in Values : \E i \in DOMAIN seq : original[i] = x => \E j \in DOMAIN seq : seq[j] = x

DomSeq(f) == { f[i] : i \in DOMAIN f }

Inv ==
  /\ todo \subseteq SUBSET (1..MaxSeqLen)
  /\ DomSeq(seq) = DomSeq(original)
  /\ \A a, b \in todo : a \cap b \neq {} => a = b
  /\ \A a, b \in todo : (\A i \in a, j \in b : i < j => seq[i] <= seq[j]) \/ (\A i \in b, j \in a : i < j => seq[i] <= seq[j])

Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] : seq = s
  /\ original = seq
  /\ todo = { {1..MaxSeqLen} }
  /\ pc = "loop"

\* One Quicksort iteration: pick an interval and either discard a singleton or
\* partition it around a chosen pivot index, nondeterministically choosing one
\* valid post-partition sequence.
Step ==
  /\ pc = "loop"
  /\ todo # {}
  /\ \E interval \in todo :
       /\ \E p \in interval :
            /\ \E s \in Partition(seq, CHOOSE lo \in interval : \A i \in interval : lo <= i,
                                     CHOOSE hi \in interval : \A i \in interval : i <= hi,
                                     p) :
                 /\ seq' = s
                 /\ todo' = (todo \ {interval}) \cup {CHOOSE lo \in interval : \A i \in interval : lo <= i..p,
                                                    CHOOSE hi \in interval : \A i \in interval : p+1..hi}
            /\ UNCHANGED <<original, pc>>
       \/ /\ Cardinality(interval) = 1
          /\ todo' = todo \ {interval}
          /\ UNCHANGED <<seq, original, pc>>

Done ==
  /\ pc = "loop"
  /\ todo = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, todo>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Done)

Termination == <>(pc = "done")

====