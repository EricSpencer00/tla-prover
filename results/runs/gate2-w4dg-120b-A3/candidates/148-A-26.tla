---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal,
  PrivateKey, PublicKey,
  Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* Types: hash iterator, block content, signature, private/public key set, node set
ASSUME NoHashVal \notin Hash
ASSUME NoBlockVal \notin Hash
ASSUME NoHash \notin Node
ASSUME NoBlock \notin Node

\* Ownership: every node's account chain is signed by the public key of its private key
VARIABLES lastHash, ledgerBy, receivedBy

vars == <<lastHash, ledgerBy, receivedBy>>

\* Ed25519 (outsourced) verifies a block's signature against the account chain owner
EdVerify(pk, block) == block.sig = pk

\* Blake2b (outsourced) calculates a fresh hash given block data and the previous hash
CalcHash(data, prev) == CalculateHash(data, prev)

\* Account-chain balance: recursively walk the chain backwards by previous hash
Balance(acc, h) ==
  IF h = NoHashVal THEN 0
  ELSE LET blk == ledgerBy[acc][h] IN
    IF blk.type = "genesis" THEN blk.amt
    ELSE IF blk.type = "send" THEN Balance(acc, blk.prev) - blk.amt
    ELSE IF blk.type = "receive" THEN Balance(acc, blk.prev) + blk.amt
    ELSE IF blk.type = "open" THEN blk.amt
    ELSE IF blk.type = "changeRep" THEN Balance(acc, blk.prev)
    ELSE Balance(acc, blk.prev)

TotalBalance == LET f[set \in SUBSET Node] ==
  IF set = {} THEN 0
  ELSE LET a == CHOOSE x \in set : TRUE IN Balance(a, lastHash) + f[set \ {a}]
  IN f[Node]

Init ==
  /\ lastHash = NoHashVal
  /\ ledgerBy = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ receivedBy = [n \in Node |-> {}]

\* Broadcast a newly created block into every node's received set
Broadcast(block) ==
  [n \in Node |-> receivedBy[n] \cup {block}]

\* A node validates a block from its received set, adding it to its local ledger
Validate(n, block) ==
  /\ block \in receivedBy[n]
  /\ EdVerify(block.key, block)
  /\ LET refPrev == ledgerBy[block.account][block.prev] IN
       /\ block.prev = NoHashVal \/ refPrev # NoBlockVal
       /\ IF block.type = "send"
            THEN block.amt <= Balance(block.account, block.prev)
          ELSE IF block.type = "receive"
            THEN refPrev.type = "send" /\ refPrev.key # block.key
          ELSE TRUE
  /\ \A m \in Node : ledgerBy[m][block.this] = NoBlockVal
  /\ ledgerBy' = [ledgerBy EXCEPT ![block.account][block.this] = block]
  /\ receivedBy' = [receivedBy EXCEPT ![n] = @ \ {block}]
  /\ UNCHANGED lastHash

\* Genesis block: adds the genesis balance into the first account's chain
GenesisBlock(n, pk) ==
  /\ lastHash = NoHashVal
  /\ ledgerBy[n][NoHashVal] = NoBlockVal
  /\ ledgerBy' = [ledgerBy EXCEPT ![n][NoHashVal] =
                    [type |-> "genesis", amt |-> GenesisBalance,
                     key |-> pk, account |-> n, prev |-> NoHashVal,
                     this |-> NoHashVal]]
  /\ lastHash' = NoHashVal
  /\ receivedBy' = Broadcast(
        [type |-> "genesis", amt |-> GenesisBalance,
         key |-> pk, account |-> n, prev |-> NoHashVal,
         this |-> NoHashVal])

\* Send block: reduces the sender's balance and designates a recipient
SendBlock(n, pk, to, amt) ==
  /\ ledgerBy[n][lastHash] # NoBlockVal
  /\ amt <= Balance(n, lastHash)
  /\ \A o \in Hash : ledgerBy[o][AmtCheck] = NoBlockVal
  /\ LET h == CalcHash([sender |-> n, recv |-> to, amt |-> amt], lastHash) IN
       /\ lastHash' = h
       /\ ledgerBy' = [ledgerBy EXCEPT ![n][h] =
            [type |-> "send", amt |-> amt, key |-> pk,
             account |-> n, prev |-> lastHash, this |-> h]]
       /\ receivedBy' = Broadcast(
            [type |-> "send", amt |-> amt, key |-> pk,
             account |-> n, prev |-> lastHash, this |-> h])

\* Open block: establishes a new account from a received send block
OpenBlock(n, pk, ref) ==
  /\ ledgerBy[n][lastHash] = NoBlockVal
  /\ \A o \in Hash: ledgerBy[o][AmtCheck] = NoBlockVal
  /\ ledgerBy[ref.account][ref.this] # NoBlockVal
  /\ ledgerBy[ref.account][ref.this].type = "send"
  /\ ledgerBy[ref.account][ref.this].key # pk
  /\ lastHash' = ref.this
  /\ ledgerBy' = [ledgerBy EXCEPT ![n][ref.this] =
       [type |-> "open", amt |-> ref.amt, key |-> pk,
        account |-> n, prev |-> NoHashVal, this |-> ref.this]]
  /\ receivedBy' = Broadcast(
       [type |-> "open", amt |-> ref.amt, key |-> pk,
        account |-> n, prev |-> NoHashVal, this |-> ref.this])

\* Receive block: adds a previously sent amount to the receiving account
ReceiveBlock(n, pk, ref) ==
  /\ ledgerBy[n][lastHash] # NoBlockVal
  /\ ledgerBy[ref.account][ref.this] # NoBlockVal
  /\ ledgerBy[ref.account][ref.this].type = "send"
  /\ ledgerBy[ref.account][ref.this].key # pk
  /\ \A o \in Hash: ledgerBy[o][AmtCheck] = NoBlockVal
  /\ lastHash' = CalcHash([ref |-> ref.this, recv |-> n], lastHash)
  /\ ledgerBy' = [ledgerBy EXCEPT ![n][lastHash] =
       [type |-> "receive", amt |-> ref.amt, key |-> pk,
        account |-> n, prev |-> lastHash, this |-> lastHash]]
  /\ receivedBy' = Broadcast(
       [type |-> "receive", amt |-> ref.amt, key |-> pk,
        account |-> n, prev |-> lastHash, this |-> lastHash])

\* Change representative: the node's voting representative changes
ChangeRep(n, pk) ==
  /\ ledgerBy[n][lastHash] # NoBlockVal
  /\ \A o \in Hash: ledgerBy[o][AmtCheck] = NoBlockVal
  /\ LET h == CalcHash([acct |-> n, prev |-> lastHash], lastHash) IN
       /\ lastHash' = h
       /\ ledgerBy' = [ledgerBy EXCEPT ![n][h] =
            [type |-> "changeRep", amt |-> 0, key |-> pk,
             account |-> n, prev |-> lastHash, this |-> h]]
       /\ receivedBy' = Broadcast(
            [type |-> "changeRep", amt |-> 0, key |-> pk,
             account |-> n, prev |-> lastHash, this |-> h])

Next ==
  \/ \E n \in Node, pk \in PrivateKey : GenesisBlock(n, pk)
  \/ \E n \in Node, pk \in PrivateKey, to \in Node, amt \in Nat : SendBlock(n, pk, to, amt)
  \/ \E n \in Node, pk \in PrivateKey, ref \in Hash : OpenBlock(n, pk, ref)
  \/ \E n \in Node, pk \in PrivateKey, ref \in Hash : ReceiveBlock(n, pk, ref)
  \/ \E n \in Node, pk \in PrivateKey : ChangeRep(n, pk)
  \/ \E n \in Node, blk \in Hash : Validate(n, ledgerBy[n][blk])

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledgerBy \in [Node -> [Hash -> [type: {"genesis", "send", "receive", "open", "changeRep"},
       amt: Nat, key: PrivateKey, account: Node, prev: Hash \cup {NoHashVal}, this: Hash \cup {NoHashVal}]]]
  /\ receivedBy \in [Node -> SUBSET Hash]

\* Both sides of the ledger must agree on the signature for every recorded block
SafetyInvariant ==
  \A n \in Node : \A blk \in {b \in Hash : ledgerBy[n][b] # NoBlockVal} :
     LET block == ledgerBy[n][blk] IN EdVerify(block.key, block)

====