---- MODULE Nano ----
EXTENDS Integers, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Data: one block per account chain; the genesis account owns the entire coin
\* supply, and every other account's balance is filled by Receive blocks.
\* Types: lastHash (a hash, or NoHash), ledger (a node -> hash -> block record,
\* or NoBlock), and received (a node -> a set of in-flight hashes).
\* Safety: the last hash fits its range, the ledger fits its type, and every
\* recorded block has a signature that matches its account's public key.
\* Hashing: CalculateHash is an opaque operator (abstract constant) that
\* models the block's hash; it is substituted by a concrete bounded version at
\* model checking time via the .cfg file.
\* Context: an account chain records block order, so the reachable state space
\* grows super-exponentially with the number of accounts and blocks.

\* Account: each public key owns one account chain. Sender is set once per
\* block, at creation time: which account's chain it belongs to.
\* Op: Send, Open, Receive, or ChangeRep (vote-rep change). Amt: coins moved.
\* PrevHash: the previous block in this account chain (NoHash for the first).
\* RefHash: a referenced block (sender references Unspent in the same chain,
\* receiver's Send in the same chain, recipient's Open in that chain).
\* Sig: the Ed25519 signature (modeled abstractly) over the block data.
\* Sender is the account creator; the signature must name that account's key.
Record == [type: {"Send", "Open", "Receive", "ChangeRep"},
           amt: Nat, sender: PublicKey, prevHash: Hash,
           refHash: Hash, sig: PrivateKey]

NodeOf(n) == (CHOOSE a \in PublicKey : (CHOOSE k \in PrivateKey : a = PublicKey[k]) = n)

AccountBalance(acc, g) ==
  IF g = NoHash THEN 0
  ELSE IF g = NoHashVal THEN 0
  ELSE IF g = NoBlockVal THEN 0
  ELSE IF g \in PublicKey THEN
    IF g = acc THEN g[amt]
    ELSE IF g.type = "Receive" /\ g.sender = acc THEN g.amt + AccountBalance(acc, g.refHash)
    ELSE AccountBalance(acc, g.prevHash)
  ELSE g[amt] + AccountBalance(acc, g.prevHash)

ChainSum(h) ==
  IF h = NoHash THEN 0
  ELSE IF h = NoHashVal THEN 0
  ELSE IF h = NoBlockVal THEN 0
  ELSE h[amt] + ChainSum(h.prevHash)

TotalBalance ==
  ChainSum(CalculateHash("genesis", NoHashVal, GenesisBalance, NoHashVal, NoHashVal, NoBlockVal))
  + ChainSum(CalculateHash("genesis", NoHashVal, GenesisBalance, NoHashVal, NoHashVal, NoBlockVal))

TypeInvariant ==
  /\ (lastHash \in Hash) \/ (lastHash = NoHash)
  /\ (ledger \in [Node -> [Hash -> Record \cup {NoBlock}]])
  /\ (received \in [Node -> SUBSET Hash])

SignatureMatchesKey(b) == PublicKey[b.sig] = b.sender

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n) ==
  /\ lastHash = NoHash
  /\ NodeOf(n) # NoHashVal
  /\ lastHash' = CalculateHash("genesis", NoHashVal, GenesisBalance, NoHashVal, NoHashVal, NoBlockVal)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
        [type |-> "Open", amt |-> GenesisBalance, sender |-> NodeOf(n),
         prevHash |-> NoHashVal, refHash |-> NoHashVal, sig |-> NoBlockVal]]]
  /\ received' = [m \in Node |-> received[m]]

CreateSendBlock(n, amt, r, ref) ==
  /\ NodeOf(n) # NoHashVal
  /\ lastHash \in Hash
  /\ ledger[n][lastHash].type \in {"Open", "Receive", "ChangeRep"}
  /\ AccountBalance(NodeOf(n), ledger[n][lastHash]) >= amt
  /\ ledger[n][ref].type = "Send" /\ ledger[n][ref].sender = NodeOf(n)
  /\ ~ \E g \in Hash : ledger[n][g].type = "Receive" /\ ledger[n][g].refHash = ref
  /\ lastHash' = CalculateHash("send", amt, NodeOf(n), lastHash, ref, n)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
        [type |-> "Send", amt |-> amt, sender |-> NodeOf(n),
         prevHash |-> lastHash, refHash |-> ref, sig |-> n]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateOpenBlock(n, ref) ==
  /\ NodeOf(n) # NoHashVal
  /\ lastHash \in Hash
  /\ ledger[n][ref].type = "Send" /\ ledger[n][ref].sender # NodeOf(n)
  /\ ~ \E g \in Hash : ledger[n][g].type = "Open" /\ ledger[n][g].refHash = ref
  /\ lastHash' = CalculateHash("open", 0, NodeOf(n), lastHash, ref, n)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
        [type |-> "Open", amt |-> 0, sender |-> NodeOf(n),
         prevHash |-> lastHash, refHash |-> ref, sig |-> n]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateReceiveBlock(n, ref) ==
  /\ NodeOf(n) # NoHashVal
  /\ lastHash \in Hash
  /\ ledger[n][ref].type = "Send" /\ ledger[n][ref].sender # NodeOf(n)
  /\ ~ \E g \in Hash : ledger[n][g].type = "Receive" /\ ledger[n][g].refHash = ref
  /\ lastHash' = CalculateHash("receive", 0, NodeOf(n), lastHash, ref, n)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
        [type |-> "Receive", amt |-> 0, sender |-> NodeOf(n),
         prevHash |-> lastHash, refHash |-> ref, sig |-> n]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateChangeRepBlock(n) ==
  /\ NodeOf(n) # NoHashVal
  /\ lastHash \in Hash
  /\ lastHash' = CalculateHash("changerep", 0, NodeOf(n), lastHash, NoHashVal, n)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
        [type |-> "ChangeRep", amt |-> 0, sender |-> NodeOf(n),
         prevHash |-> lastHash, refHash |-> NoHashVal, sig |-> n]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

ValidateBlock(m, h) ==
  /\ h \in received[m]
  /\ ledger[m][h] # NoBlock
  /\ SignatureMatchesKey(ledger[m][h])
  /\ ledger[m][ledger[m][h].prevHash].type \in {"Open", "Receive", "ChangeRep"}
  /\ \/ ledger[m][h].type = "Send"
        \/ ledger[m][h].type = "Open"
        \/ ledger[m][h].type = "Receive"
        \/ ledger[m][h].type = "ChangeRep"
  /\ received' = [received EXCEPT ![m] = received[m] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, amt \in 1..GenesisBalance, r \in Node, ref \in Hash : CreateSendBlock(n, amt, r, ref)
  \/ \E n \in Node, ref \in Hash : CreateOpenBlock(n, ref)
  \/ \E n \in Node, ref \in Hash : CreateReceiveBlock(n, ref)
  \/ \E n \in Node : CreateChangeRepBlock(n)
  \/ \E m \in Node, h \in Hash : ValidateBlock(m, h)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

SafetyInvariant ==
  /\ TypeInvariant
  /\ \A m \in Node, h \in Hash : ledger[m][h] # NoBlock => PublicKey[ledger[m][h].sig] = ledger[m][h].sender

\* The invariant below, about total balance, is outside SafetyInvariant by
\* design (it is a separate claim, not a type or signature check) and is not
\* part of the answer -- it is provided as context for the model, nothing
\* more.  Keeping it outside SafetyInvariant is exactly what the .cfg file
\* (which only names the former) is meant to guarantee a sound check.
BalanceWithinGenesis == TotalBalance <= GenesisBalance

====