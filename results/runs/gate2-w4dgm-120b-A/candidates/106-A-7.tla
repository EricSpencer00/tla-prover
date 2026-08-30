---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS

SPECIFICATION ==
  /\ \A a, b \in SUBSET Nat : (a \cap b # {}) => (a # {} /\ b # {})
  /\ \A s \in SUBSET Nat : s # {} => (\E x \in s : \A y \in s : y <= x)
  /\ \A s \in SUBSET Nat : s # {} => (\E x \in s : \A y \in s : y >= x)
  /\ \A s \in SUBSET Nat, f \in [Nat -> Nat] : \E x \in s : \A y \in s : f[y] = f[x]
  /\ \A s \in SUBSET (SUBSET Nat) : \E x \in s : \A y \in s : x \cap y = {}
  /\ \A s \in SUBSET Nat, f \in [Nat -> Nat] : \E r \in Nat :
        \E foldRes \in Nat :
          /\ foldRes = \E x \in s : f[x]
          /\ r = foldRes

Init ==
  /\ TRUE

Next ==
  /\ TRUE

INVARIANTS ==
  /\ TRUE

PROPERTIES ==
  /\ TRUE

Index(seq, e) == CHOOSE k \in DOMAIN seq : seq[k] = e
SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}
Permutations(s) == {p \in Seq(s) : Cardinality(s) = Len(p)
  /\ \A i, j \in DOMAIN p : p[i] = p[j] => i = j}

====