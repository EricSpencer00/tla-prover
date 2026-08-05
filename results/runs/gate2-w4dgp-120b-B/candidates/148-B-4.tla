---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
  Hash, CalculateHash(_,_,_), PrivateKey, PublicKey, KeyPair, Node,
  GenesisBalance, Ownership

VARIABLES lastHash, distributedLedger, received

ASSUME
  /\ \A data, old, new : CalculateHash(data, old, new) \in BOOLEAN
  /\ KeyPair \in [PrivateKey -> PublicKey]
  /\ GenesisBalance \in Nat
  /\ Ownership \in [Node -> PrivateKey]

Signature == [data : Hash, signedWith : PrivateKey]
NoBlock == CHOOSE s \in Signature : FALSE
NoHash == CHOOSE h \in Hash : FALSE

Ledger == [Hash -> Signature \cup {NoBlock}]
Block == [type : {"genesis","open","send","receive","change"}, account : PublicKey,
          balance : Nat, destination : PublicKey, previous : Hash, source : Hash,
          rep : PublicKey]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ distributedLedger \in [Node -> [Hash -> Signature \cup {NoBlock}]]
  /\ received \subseteq Signature

RECURSIVE BalanceAt(_)
BalanceAt(s, h) ==
  LET b == s[h] IN
  IF b = NoBlock THEN 0
  ELSE IF b.type = "send" THEN b.balance
  ELSE IF b.type \in {"open","receive"} THEN BalanceAt(s, b.previous) + b.balance
  ELSE BalanceAt(s, b.previous)

RECURSIVE SumBag(_)
SumBag(b) ==
  LET set == BagToSet(b) IN
  IF set = {} THEN 0
  ELSE LET x == CHOOSE y \in set : TRUE IN x + SumBag(b \ {x})

BalanceInvariant ==
  \A n \in Node : SumBag(BagOfAll(BalanceAt(distributedLedger[n]), Hash)) <= GenesisBalance

Spec ==
  /\ TypeOK
  /\ BalanceInvariant

====