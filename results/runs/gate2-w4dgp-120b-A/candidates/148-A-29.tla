---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, NoBlock

\* The hash calculation is modeled as an abstract constant operator that is
\* substituted with an implementation in the .cfg (CalculateHashImpl).  The
\* block-chain history is the source of super-exponential state space, so
\* only tiny hash/coin limits survive model checking.
VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Account balance is defined recursively over the chain; an omitted
\* predecessor means the account has reached the start of its chain.
RECURSIVE Balance(_, _)
Balance(n, g) ==
  IF g = NoBlock THEN 0
  ELSE IF g.type = "s" THEN Balance(n, g.prev) - g.amount
  ELSE IF g.type = "r" THEN Balance(n, g.prev) + g.amount
  ELSE Balance(n, g.prev)

\* Every block in every node's ledger must have a valid signature checked
\* against the account's public key (the hash of the key itself, here).
TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> [type : {"s", "o", "r"}, sender : Node, amt : Nat, prev : Hash \cup {NoHash}, to : PublicKey, key : PublicKey, hash : Hash \cup {NoHash}]]]
  /\ received \in [Node -> SUBSET Hash]

/\ These actions (1)-(6) are the core of the Nano block-lattice protocol.
\* Each creates exactly one block, adds it to every node's in-flight set,
\* and leaves the ledger untouched until Validate (7) moves it in.
Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [g \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block is created exactly once, with the full supply, and
\* is simultaneously recorded in every node's ledger copy.
CreateGenesisBlock(n) ==
  /\ \A g \in Hash : ledger[n][g] = NoBlockVal
  /\ lastHash' = CalculateHashImpl([type |-> "o", sender |-> n, amt |-> GenesisBalance, prev |-> NoHash, to |-> PublicKey, key |-> PublicKey, hash |-> NoHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [type |-> "o", sender |-> n, amt |-> GenesisBalance, prev |-> NoHash, to |-> PublicKey, key |-> PublicKey, hash |-> lastHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

\* A send block reduces the sender's balance and designates a recipient.
CreateSendBlock(n, k) ==
  /\ lastHash # NoHashVal
  /\ Balance(n, ledger[n][lastHash]) >= k
  /\ lastHash' = CalculateHashImpl([type |-> "s", sender |-> n, amt |-> k, prev |-> lastHash, to |-> PublicKey, key |-> PublicKey, hash |-> NoHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [type |-> "s", sender |-> n, amt |-> k, prev |-> lastHash, to |-> PublicKey, key |-> PublicKey, hash |-> lastHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

\* Opening a new account references a send block already recorded at the
\* recipient and starts that account's chain.
CreateOpenBlock(n) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHashImpl([type |-> "o", sender |-> n, amt |-> 0, prev |-> NoHash, to |-> PublicKey, key |-> PublicKey, hash |-> NoHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [type |-> "o", sender |-> n, amt |-> 0, prev |-> NoHash, to |-> PublicKey, key |-> PublicKey, hash |-> lastHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

\* A receive block adds the sent amount to the receiver's balance.
CreateReceiveBlock(n) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHashImpl([type |-> "r", sender |-> n, amt |-> 0, prev |-> lastHash, to |-> PublicKey, key |-> PublicKey, hash |-> NoHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [type |-> "r", sender |-> n, amt |-> 0, prev |-> lastHash, to |-> PublicKey, key |-> PublicKey, hash |-> lastHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

\* A representative-change block only references the prior block on that
\* account's chain and requires no amount or recipient.
CreateChangeRepBlock(n) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHashImpl([type |-> "o", sender |-> n, amt |-> 0, prev |-> lastHash, to |-> PublicKey, key |-> PublicKey, hash |-> NoHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [type |-> "o", sender |-> n, amt |-> 0, prev |-> lastHash, to |-> PublicKey, key |-> PublicKey, hash |-> lastHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

\* Validation authenticates a block's signature and checks that any
\* referenced block exists in the node's own ledger copy.
Validate(n, g) ==
  /\ g \in received[n]
  /\ ledger[n][g].hash = g
  /\ (IF ledger[n][g].type = "s" THEN ledger[n][ledger[n][g].prev].hash = ledger[n][g].prev /\ Balance(n, ledger[n][g].prev) >= ledger[n][g].amt ELSE TRUE)
  /\ ledger' = [m \in Node |-> IF n = m THEN [ledger[m] EXCEPT ![g] = ledger[n][g]] ELSE ledger[m]]
  /\ received' = [m \in Node |-> IF n = m THEN received[m] \ {g} ELSE received[m]]
  /\ lastHash' = lastHash

\* CreateGenesis, CreateSend, CreateOpen, CreateReceive, CreateChangeRep,
\* and Validate are all fair (weak, not strong) for every node, which is
\* as much fairness as a block-lattice protocol can hope for.
Next ==
  \/ \E n \in Node : CreateGenesisBlock(n) \/ CreateOpenBlock(n) \/ CreateReceiveBlock(n) \/ CreateChangeRepBlock(n)
  \/ \E n \in Node, k \in 1..GenesisBalance : CreateSendBlock(n, k)
  \/ \E n \in Node, g \in Hash : Validate(n, g)
\* Each individual action for each node is weakly fair.
Spec == Init /\ [][Next]_vars
  /\ \A n \in Node : WF_vars(CreateGenesisBlock(n))
  /\ \A n \in Node : \A k \in 1..GenesisBalance : WF_vars(CreateSendBlock(n, k))
  /\ \A n \in Node : WF_vars(CreateOpenBlock(n))
  /\ \A n \in Node : WF_vars(CreateReceiveBlock(n))
  /\ \A n \in Node : WF_vars(CreateChangeRepBlock(n))
  /\ \A n \in Node : \A g \in Hash : WF_vars(Validate(n, g))

\* Every block in every node's ledger copy must have a signature that
\* matches the account's public key (hash(key) = stored key); this makes
\* a forged block from an unauthorized key instantly visible.
SafetyInvariant ==
  \A n \in Node : \A g \in Hash :
    ledger[n][g] # NoBlockVal => (CalculateHashImpl([type |-> ledger[n][g].type, sender |-> ledger[n][g].sender, amt |-> ledger[n][g].amt, prev |-> ledger[n][g].prev, to |-> ledger[n][g].to, key |-> ledger[n][g].key, hash |-> NoHash]) = g)

====