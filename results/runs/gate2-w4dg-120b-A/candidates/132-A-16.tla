---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

\* The distinct model values are A, B, C, and the bound controls the
\* maximum sequence length.  Seq is the finite set of sequences; the
\* bound and the choice of a concrete value set keep the model finite
\* for exhaustive checking with TLC.

Values == {A, B, C}

DomainOf(s) == IF s = {} THEN 0 ELSE (CHOOSE n \in DOMAIN s : \A k \in DOMAIN s : k <= n)

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in Seq
  /\ pos \in 0..DomainOf(seq)
  /\ cand \in Values \cup {"none"}
  /\ count \in 0..bound

Init ==
  /\ \E s \in Seq : seq = s
  /\ pos = 1
  /\ \E e \in Values : cand = e
  /\ count = 0

\* The three-case scan of the Boyer-Moore majority vote algorithm:
\* adopt a new candidate when the counter is zero, increment when the
\* next element matches the candidate, or decrement otherwise.
Step ==
  /\ pos <= DomainOf(seq)
  /\ LET c == seq[pos] IN
       /\ (count = 0 /\ cand' = c /\ count' = 1)
       \/ (cand = c /\ cand' = cand /\ count' = count + 1)
       \/ (cand # c /\ count > 0 /\ cand' = cand /\ count' = count - 1)
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

Correct ==
  (count > 0 /\ cand \in Values) => \E e \in Values :
     cand = e /\ 2 * Cardinality({i \in DOMAIN seq : seq[i] = e}) > DomainOf(seq)

Inv == \A a \in Values, n \in 1..DomainOf(seq) :
         (2 * Cardinality({i \in DOMAIN seq : i <= n /\ seq[i] = a}) > n) => cand = a

====