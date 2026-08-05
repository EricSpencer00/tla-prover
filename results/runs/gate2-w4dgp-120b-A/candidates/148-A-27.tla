---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  \* Hash is the finite set of possible block hashes; NoHashVal is the hash-sentinel value meaning "no block exists yet."
  \* PrivateKey and PublicKey are the key pairs of the network nodes; Node is the set of network participants.
  \* GenesisBalance is the total amount of coins in the system, and NoBlockVal is the sentinel for an empty block slot.
  \* CalculateHash is a placeholder for a hash function that must be concretized in the .cfg (CalculateHashImpl).
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash
CONSTANT CalculateHash

\* A block is defined by its type, the creator's public key, its own hash, the hash of the previous block in the
\* creator's chain, the hash of the block it receives (for receive blocks), the amount transferred, and the next
\* block in the chain (for walking the chain in balance calculations).
Blocks == {
  ttype: {"genesis", "send", "open", "receive", "change"},
  signer: PublicKey,
  hash: Hash,
  prevHash: Hash \cup {NoHash},
  recvHash: Hash \cup {NoHashVal},
  amount: 0..GenesisBalance,
  next: Hash \cup {NoBlockVal}
}

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

\* Recursive function that walks an account chain from the first hash down to the end and sums the amounts.
RECURSIVE SumChain(_)
SumChain(S) ==
  IF S = {} THEN 0
  ELSE LET b == CHOOSE x \in S : TRUE IN b.amount + SumChain(S \ {b})

\* BalanceOf computes the total balance of the account identified by a public key on a particular node's ledger.
RECURSIVE BalanceOf(_, _)
BalanceOf(node, pub) ==
  LET first == CHOOSE b \in {x \in ledger[node] : x.signer = pub /\ x.prevHash = NoHash} : TRUE
  IN LET recurse(f) ==
       IF f = NoBlockVal THEN 0
       ELSE LET cur == CHOOSE x \in {x \in ledger[node] : x.hash = f} : TRUE
            IN cur.amount + recurse(cur.next)
     IN recurse(first.hash)

\* The sum of all account balances never exceeds the total coin supply; defined separately from the main invariant.
TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Blocks \cup {{}}]]
  /\ received \in [Node -> SUBSET Hash]

\* Every block recorded in every node's ledger must have a signature that matches the public key of the account
\* owning the block's chain, and no node may ever hold more than the genesis balance across all accounts.
SafetyInvariant ==
  /\ \A node \in Node, h \in Hash :
       ledger[node][h] # {{}} =>
         LET b == CHOOSE x \in ledger[node][h] : TRUE IN b.signer \in {PublicKey[p] : p \in PrivateKey}
  /\ \A node \in Node : SumChain(LET S == {x \in ledger[node] : x # {{}}} IN S) <= GenesisBalance

TypeInvariant == TypeOK

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> {{}}]]
  /\ received = [n \in Node |-> {}]

\* CreateGenesisBlock produces the very first block in the entire block lattice and stamps the full genesis
\* supply into it. It can only fire while no other block exists (lastHash = NoHashVal).
CreateGenesisBlock(p) ==
  /\ lastHash = NoHashVal
  /\ p \in PrivateKey
  /\ LET b == [ttype |-> "genesis", signer |-> PublicKey[p], hash |-> CalculateHash(PAIR(2, NoHashVal)), prevHash |-> NoHash, recvHash |-> NoHashVal, amount |-> GenesisBalance, next |-> NoBlockVal] IN
       /\ lastHash' = b.hash
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![b.hash] = {b}]]
       /\ received' = [n \in Node |-> {b.hash}]

\* CreateSendBlock reduces the creator's account balance and designates a recipient; the sender must have
\* enough balance to cover the transfer. The block is broadcast to every node's received set.
CreateSendBlock(p, amount, recv) ==
  /\ p \in PrivateKey
  /\ amount > 0
  /\ lastHash # NoHashVal
  /\ BalanceOf(ANY, PublicKey[p]) >= amount
  /\ LET b == [ttype |-> "send", signer |-> PublicKey[p], hash |-> CalculateHash(PAIR(2, lastHash)), prevHash |-> lastHash, recvHash |-> NoHashVal, amount |-> amount, next |-> NoBlockVal] IN
       /\ lastHash' = b.hash
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![b.hash] = {b}]]
       /\ received' = [n \in Node |-> @ \cup {b.hash}]

\* CreateOpenBlock establishes a brand-new account chain for a node that has no chain yet, referencing a
\* specific send block that was addressed to its public key.
CreateOpenBlock(p, recvHash) ==
  /\ p \in PrivateKey
  /\ lastHash # NoHashVal
  /\ \A n \in Node : {b \in ledger[n] : b.signer = PublicKey[p]} = {}
  /\ \E n \in Node, b \in ledger[n] : b.signer = PublicKey[p] /\ b.hash = recvHash /\ b.ttype = "send"
  /\ LET b == [ttype |-> "open", signer |-> PublicKey[p], hash |-> CalculateHash(PAIR(2, NoHashVal)), prevHash |-> NoHash, recvHash |-> recvHash, amount |-> 0, next |-> NoBlockVal] IN
       /\ lastHash' = b.hash
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![b.hash] = {b}]]
       /\ received' = [n \in Node |-> @ \cup {b.hash}]

\* CreateReceiveBlock adds a previously-received amount to an account, referencing the send block directly
\* and the previous block in the receiver's own chain.
CreateReceiveBlock(p, sendHash) ==
  /\ p \in PrivateKey
  /\ lastHash # NoHashVal
  /\ \E n \in Node, b \in ledger[n] : b.signer = PublicKey[p] /\ b.prevHash = NoHash
  /\ \E n \in Node, b \in ledger[n] :
       b.signer = PublicKey[p] /\ b.ttype = "send" /\ b.hash = sendHash /\ b.amount > 0
  /\ LET b == [ttype |-> "receive", signer |-> PublicKey[p], hash |-> CalculateHash(PAIR(2, lastHash)), prevHash |-> lastHash, recvHash |-> sendHash, amount |-> 0, next |-> NoBlockVal] IN
       /\ lastHash' = b.hash
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![b.hash] = {b}]]
       /\ received' = [n \in Node |-> @ \cup {b.hash}]

\* CreateChangeRepresentativeBlock generates a block that re-points the account's voting weight to a new
\* representative without moving any funds.
CreateChangeBlock(p) ==
  /\ p \in PrivateKey
  /\ lastHash # NoHashVal
  /\ LET b == [ttype |-> "change", signer |-> PublicKey[p], hash |-> CalculateHash(PAIR(2, lastHash)), prevHash |-> lastHash, recvHash |-> NoHashVal, amount |-> 0, next |-> NoBlockVal] IN
       /\ lastHash' = b.hash
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![b.hash] = {b}]]
       /\ received' = [n \in Node |-> @ \cup {b.hash}]

\* ProcessBlock validates a received block against the node's own copy of the ledger before adding it, and
\* clears the block from the received set on success.
ProcessBlock(node, hash) ==
  /\ hash \in received[node]
  /\ \E b \in ledger[node][hash] :
       /\ b.signer \in {PublicKey[p] : p \in PrivateKey}
       /\ b.ttype \in {"genesis", "send", "open", "receive", "change"}
       /\ (b.ttype = "send" => BalanceOf(node, b.signer) >= b.amount)
       /\ (b.ttype = "open" => \E n \in Node, s \in ledger[n] : s.signer = b.signer /\ s.ttype = "send" /\ s.hash = b.recvHash)
       /\ (b.ttype = "receive" => \E n \in Node, s \in ledger[n] : s.signer = b.signer /\ s.ttype = "send" /\ s.hash = b.recvHash /\ s.amount > 0)
  /\ ledger' = [ledger EXCEPT ![node][hash] = @]
  /\ received' = [received EXCEPT ![node] = @ \ {hash}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E p \in PrivateKey : CreateGenesisBlock(p)
  \/ \E p \in PrivateKey, a \in 1..GenesisBalance, r \in Node : CreateSendBlock(p, a, r)
  \/ \E p \in PrivateKey, h \in Hash : CreateOpenBlock(p, h)
  \/ \E p \in PrivateKey, h \in Hash : CreateReceiveBlock(p, h)
  \/ \E p \in PrivateKey : CreateChangeBlock(p)
  \/ \E node \in Node, h \in Hash : ProcessBlock(node, h)

Spec == Init /\ [][Next]_vars

====