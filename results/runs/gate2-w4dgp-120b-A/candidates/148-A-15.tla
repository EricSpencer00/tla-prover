---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

\* Nano cryptocurrency: each account has its own chain of blocks. The spec
\* models hash functions and signatures and shows why finite model checking
\* of blockchain history (which records action order in the chain itself)
\* is only feasible when the action space is artificially constrained.
CONSTANTS
  Hash, NoHashVal
  PrivateKey, PublicKey
  Node
  GenesisBalance
  NoBlockVal
  CalculateHash
  NoHash
  NoBlock

VARIABLES
  lastHash
  ledger
  recv

vars == <<lastHash, ledger, recv>>

AccountOf(h) == IF h \in Hash THEN PublicKey ELSE NoHashVal

Balance(n) ==
  LET Chain == {h \in Hash : ledger[n][h] # NoBlockVal}
      Amounts == {IF ledger[n][h].type = "send" THEN ledger[n][h].amount ELSE 0 : h \in Chain}
  IN IF Chain = {} THEN 0 ELSE LET m == CHOOSE x \in Chain : \A y \in Chain : ledger[n][x].seq >= ledger[n][y].seq IN Amounts[m]

Quiescent(n) == \A h \in Hash : (h \in recv[n]) => ledger[n][h] # NoBlockVal

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> [type: {"genesis", "send", "open", "receive", "change"}, src: PublicKey, dst: PublicKey, amount: Nat, seq: Nat, sig: PrivateKey]]] \cup {NoBlockVal}
  /\ recv \subseteq [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ recv = [n \in Node |-> {}]

\* A block is signed with the sender's private key and its hash is calculated
\* from its contents plus the previous hash, so the same contents never repeat.
CreateBlock(n, t, dst, amt) ==
  /\ t \in {"send", "open", "receive", "change"}
  /\ amt \in 1..GenesisBalance
  /\ lastHash \in Hash \cup {NoHash}
  /\ let srcKey == AccountOf(lastHash) in
     LET b ==
       [type |-> t, src |-> srcKey, dst |-> dst, amount |-> amt, seq |-> IF lastHash = NoHash THEN 1 ELSE ledger[n][lastHash].seq + 1, sig |-> n]
         IN LET hash == CalculateHash(b, lastHash) IN
            /\ hash \notin Hash
            /\ lastHash' = hash
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![hash] = b]]
            /\ recv' = [m \in Node |-> recv[m] \cup {hash}]

CreateGenesis(n) ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ recv = [n \in Node |-> {}]
  /\ let b == [type |-> "genesis", src |-> NoHashVal, dst |-> NoHashVal, amount |-> GenesisBalance, seq |-> 1, sig |-> n]
         IN LET hash == CalculateHash(b, NoHash) IN
            /\ hash \notin Hash
            /\ lastHash' = hash
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![hash] = b]]
            /\ recv' = [m \in Node |-> recv[m] \cup {hash}]

ProcessBlock(n) ==
  /\ \E h \in recv[n] : ledger[n][h] # NoBlockVal
  /\ LET h == CHOOSE x \in recv[n] : ledger[n][x] # NoBlockVal
     IN /\ ledger[n][h].sig = n
        /\ ledger[n][h].src # NoHashVal => ledger[n][ledger[n][h].src].type \notin {"send", "open"}
        /\ ledger[n][h].type \notin {"send", "open"}
        /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
        /\ recv' = [recv EXCEPT ![n] = recv[n] \ {h}]
        /\ UNCHANGED lastHash

Next == \E n \in Node : CreateGenesis(n) \/ ProcessBlock(n)
        \/ \E t \in {"send", "open", "receive", "change"} : \E n \in Node : \E d \in PublicKey : \E a \in 1..GenesisBalance : CreateBlock(n, t, d, a)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must have a valid signature.
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sig = n

====