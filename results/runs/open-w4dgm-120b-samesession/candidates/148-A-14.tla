---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Replacements: CalculateHashImpl is substituted by the .cfg for CalculateHash,
\* so the model actually runs with a finite, tractable version of the hash op.
CalculateHashImpl == CalculateHash

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Balance of an account is computed by walking its chain backwards from the
\* last block, adding (send) or subtracting (receive) according to block type.
RECURSIVE Balance(_)
Balance(h) ==
  IF h = NoHash THEN 0
  ELSE LET blk == ledger[NoHash][h] IN
       IF blk = NoBlockVal THEN 0
       ELSE IF blk.type = "send" THEN -blk.amount + Balance(blk.prevHash)
       ELSE IF blk.type = "receive" THEN blk.amount + Balance(blk.prevHash)
       ELSE Balance(blk.prevHash)

\* Total balance of all accounts in this spec's bounded model.
RECURSIVE TotalOf(_)
TotalOf(S) ==
  IF S = {} THEN 0
  ELSE LET h == CHOOSE x \in S : TRUE IN Balance(h) + TotalOf(S \ {h})

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> [owner: Node, type: {"send", "receive", "open", "change", "genesis"}, amount: 0..GenesisBalance, prevHash: Hash \cup {NoHash}, dest: PublicKey \cup {NoHash}, signature: PublicKey \cup {NoHash}]]]
  /\ received \in [Node -> SUBSET [hash: Hash, block: [owner: Node, type: {"send", "receive", "open", "change", "genesis"}, amount: 0..GenesisBalance, prevHash: Hash \cup {NoHash}, dest: PublicKey \cup {NoHash}, signature: PublicKey \cup {NoHash}]]]

\* Every block in every node's ledger must have a signature that matches the
\* public key of the account chain it belongs to.
SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].signature = PublicKey[n]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n) ==
  /\ lastHash = NoHash
  /\ ~\E h \in Hash : ledger[n][h] # NoBlockVal
  /\ LET h == CalculateHashImpl([owner |-> n, type |-> "genesis", amount |-> GenesisBalance, prevHash |-> NoHash, dest |-> NoHash]) IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [owner |-> n, type |-> "genesis", amount |-> GenesisBalance, prevHash |-> NoHash, dest |-> NoHash, signature |-> PublicKey[n]]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> h, block |-> [owner |-> n, type |-> "genesis", amount |-> GenesisBalance, prevHash |-> NoHash, dest |-> NoHash, signature |-> PublicKey[n]]]}]

CreateSendBlock(n, amt, dst) ==
  /\ lastHash # NoHash
  /\ Balance(lastHash) >= amt
  /\ LET h == CalculateHashImpl([owner |-> n, type |-> "send", amount |-> amt, prevHash |-> lastHash, dest |-> dst]) IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [owner |-> n, type |-> "send", amount |-> amt, prevHash |-> lastHash, dest |-> dst, signature |-> PublicKey[n]]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> h, block |-> [owner |-> n, type |-> "send", amount |-> amt, prevHash |-> lastHash, dest |-> dst, signature |-> PublicKey[n]]]}]

CreateOpenBlock(n, h, amt) ==
  /\ lastHash # NoHash
  /\ ledger[n][h] = NoBlockVal
  /\ ledger[n][h].type = "send"
  /\ ledger[n][h].dest = PublicKey[n]
  /\ ledger[n][h].amount = amt
  /\ LET g == CalculateHashImpl([owner |-> n, type |-> "open", amount |-> amt, prevHash |-> NoHash, dest |-> NoHash]) IN
       /\ lastHash' = g
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![g] = [owner |-> n, type |-> "open", amount |-> amt, prevHash |-> NoHash, dest |-> NoHash, signature |-> PublicKey[n]]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> g, block |-> [owner |-> n, type |-> "open", amount |-> amt, prevHash |-> NoHash, dest |-> NoHash, signature |-> PublicKey[n]]]}]

CreateReceiveBlock(n, h, amt) ==
  /\ lastHash # NoHash
  /\ ledger[n][h] = NoBlockVal
  /\ ledger[n][h].type = "send"
  /\ ledger[n][h].dest = PublicKey[n]
  /\ ledger[n][h].amount = amt
  /\ LET g == CalculateHashImpl([owner |-> n, type |-> "receive", amount |-> amt, prevHash |-> lastHash, dest |-> NoHash]) IN
       /\ lastHash' = g
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![g] = [owner |-> n, type |-> "receive", amount |-> amt, prevHash |-> lastHash, dest |-> NoHash, signature |-> PublicKey[n]]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> g, block |-> [owner |-> n, type |-> "receive", amount |-> amt, prevHash |-> lastHash, dest |-> NoHash, signature |-> PublicKey[n]]]}]

CreateChangeBlock(n) ==
  /\ lastHash # NoHash
  /\ LET h == CalculateHashImpl([owner |-> n, type |-> "change", amount |-> 0, prevHash |-> lastHash, dest |-> NoHash]) IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [owner |-> n, type |-> "change", amount |-> 0, prevHash |-> lastHash, dest |-> NoHash, signature |-> PublicKey[n]]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> h, block |-> [owner |-> n, type |-> "change", amount |-> 0, prevHash |-> lastHash, dest |-> NoHash, signature |-> PublicKey[n]]]}]

ValidateBlock(n, r) ==
  /\ r \in received[n]
  /\ received' = [received EXCEPT ![n] = @ \ {r}]
  /\ ledger' = [ledger EXCEPT ![n][r.hash] =
        IF r.block.destination = PublicKey[n] THEN r.block
        ELSE IF r.block.dest # NoHash THEN ledger[n][r.block.dest]
        ELSE ledger[n][r.block.prevHash]]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n) \/ CreateChangeBlock(n)
  \/ \E n \in Node, amt \in 1..GenesisBalance, dst \in PublicKey : CreateSendBlock(n, amt, dst)
  \/ \E n \in Node, h \in Hash, amt \in 1..GenesisBalance : CreateOpenBlock(n, h, amt) \/ CreateReceiveBlock(n, h, amt)
  \/ \E n \in Node, r \in [hash: Hash, block: [owner: Node, type: {"send", "receive", "open", "change", "genesis"}, amount: 0..GenesisBalance, prevHash: Hash \cup {NoHash}, dest: PublicKey \cup {NoHash}, signature: PublicKey \cup {NoHash}]] : ValidateBlock(n, r)

Spec == Init /\ [][Next]_vars

====