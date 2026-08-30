---- MODULE Nano ----
EXTENDS Naturals, Sequences

\* Ed25519-style signatures: a private key holder signs a block, and
\* SafetyInvariant checks that the recorded signature matches the public
\* key of the account whose chain the block resides in.
\* Blake2b-style hashing: CalculateHash is the abstract hash operator.
\* Blocks are appended in order, so each account's chain is a sequence of
\* blocks whose length is the account's current balance; the block chain
\* itself is the balance record, so model checking (which visits literal
\* states) cannot explore a super-exponential range of action orders.

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* LastHash is the last calculated block hash, used for ordering.
\* Ledger is the replicated ledger; each node's copy maps hashes to signed
\* blocks (or NoBlockVal). Received is the set of broadcast blocks waiting
\* to be validated by each node.
VARIABLES LastHash, Ledger, Received
vars == <<LastHash, Ledger, Received>>

\* A block is a signed action, typed by the account (public key) it belongs
\* to, carrying a hash, a reference to the previous block in that account's
\* chain, its type, and the signature of its creator.
Block == [acct: PublicKey, hash: Hash, prev: Hash, tag: {"genesis", "send", "open", "receive", "change"}, sig: PrivateKey]

TypeOK ==
  /\ LastHash \in Hash \cup {NoHash}
  /\ Ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ Received \in [Node -> SUBSET Block]

\* The per-account sequences of blocks are held in the ledger's per-hash
\* map; a block's timestamp is its index in that sequence, so private
\* Balance functions below are literally summing over its chain to compute
\* the account's current balance.
\* SenderBalance uses the ledger of the node that owns the sending account.
\* ReceiverBalance counts how many receive blocks have already claimed a
\* particular send block, to enforce "single spend per send" at validation.
SequenceOf(a, h) == CHOOSE seq \in Seq(Block) : \A i \in DOMAIN seq : seq[i].hash = h /\ seq[i].acct = a
SenderBalance(sender, node) ==
  IF SenderChain(sender) = <<>> THEN 0
  ELSE Len(SequenceOf(sender, SenderChain(sender)))
ReceiverBalance(receiver, node) ==
  LET claimed == {b \in Ledger[node] : b.tag = "receive" /\ b.prev = receiver}
  IN Cardinality(claimed)

\* Account chains are defined by following each block's previous-hash link
\* back to NoHash. The chain is a sequence, so order is preserved and
\* reflected in the balance directly; this is exactly what makes the
\* block lattice's state space blow up super-exponentially.
ChainHashes(a) ==
  LET head == CHOOSE h \in Hash : Ledger[CHOOSE n \in Node : TRUE][h] # NoBlockVal /\ Ledger[CHOOSE n \in Node : TRUE][h].acct = a /\ Ledger[CHOOSE n \in Node : TRUE][h].prev = NoHash
  IN head \o ChainHashesRec(a, head)
ChainHashesRec(a, h) ==
  IF \E n \in Node : Ledger[n][h].tag = "receive" /\ Ledger[n][h].prev # NoHash
  THEN LET nxt == CHOOSE z \in Hash : \E n \in Node : Ledger[n][z].tag = "receive" /\ Ledger[n][z].prev = h /\ Ledger[n][z].acct = a
       IN nxt \o ChainHashesRec(a, nxt)
  ELSE <<>>

\* The genesis account is the only account with balance at the start, so
\* its balance is the system's total coin supply and nothing can exceed it.
GenesisAcct == CHOOSE pk \in PublicKey : TRUE

Init ==
  /\ LastHash = NoHash
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ Received = [n \in Node |-> {}]

\* CreateGenesisBlock is the single starting point of the lattice; it
\* appends the initial chain node on every replica at once, so no replica
\* can lag behind the moment the coin supply exists.
CreateGenesisBlock(creator) ==
  /\ LastHash = NoHash
  /\ LastHash' = CalculateHash([acct |-> GenesisAcct, prev |-> NoHash, tag |-> "genesis"], NoHash)
  /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![LastHash] = [acct |-> GenesisAcct, hash |-> LastHash, prev |-> NoHash, tag |-> "genesis", sig |-> creator]]]
  /\ Received' = [n \in Node |-> {}]

CreateSendBlock(node, sender, recipient, k) ==
  /\ SenderBalance(sender, node) >= k
  /\ LastHash' = CalculateHash([acct |-> sender, prev |-> SenderChain(sender), tag |-> "send"], LastHash)
  /\ Ledger' = [n \in Node |> [Ledger[n] EXCEPT ![LastHash] = [acct |-> sender, hash |-> LastHash, prev |-> SenderChain(sender), tag |-> "send", sig |-> node]]]
  /\ Received' = [n \in Node |-> Received[n] \cup {[acct |-> sender, hash |-> LastHash, prev |-> SenderChain(sender), tag |-> "send", sig |-> node]}]

CreateOpenBlock(node, recipient) ==
  /\ SenderBalance(recipient, node) = 0
  /\ \E h \in Hash : \E n \in Node :
       /\ Ledger[n][h].tag = "send" /\ Ledger[n][h].acct # recipient
       /\ Ledger[n][h] \notin Received[node]
       /\ LastHash' = CalculateHash([acct |-> recipient, prev |-> NoHash, tag |-> "open"], LastHash)
       /\ Ledger' = [m \in Node |-> [Ledger[m] EXCEPT ![LastHash] = [acct |-> recipient, hash |-> LastHash, prev |-> NoHash, tag |-> "open", sig |-> node]]]
       /\ Received' = [m \in Node |-> IF m = node THEN Received[m] \cup {Ledger[n][h]} ELSE Received[m]]
  /\ TRUE

CreateReceiveBlock(node, receiver, sender) ==
  /\ ReceiverBalance(receiver, node) < SenderBalance(sender, node)
  /\ LastHash' = CalculateHash([acct |-> receiver, prev |-> SenderChain(receiver), tag |-> "receive"], LastHash)
  /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![LastHash] = [acct |-> receiver, hash |-> LastHash, prev |-> SenderChain(receiver), tag |-> "receive", sig |-> node]]]
  /\ Received' = [n \in Node |-> Received[n] \cup {[acct |-> receiver, hash |-> LastHash, prev |-> SenderChain(receiver), tag |-> "receive", sig |-> node]}]

CreateChangeRepBlock(node, acct) ==
  /\ SenderBalance(acct, node) > 0
  /\ LastHash' = CalculateHash([acct |-> acct, prev |-> SenderChain(acct), tag |-> "change"], LastHash)
  /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![LastHash] = [acct |-> acct, hash |-> LastHash, prev |-> SenderChain(acct), tag |-> "change", sig |-> node]]]
  /\ Received' = [n \in Node |-> Received[n] \cup {[acct |-> acct, hash |-> LastHash, prev |-> SenderChain(acct), tag |-> "change", sig |-> node]}]

\* Validation checks the signature, the existence of the previous block,
\* and the tag-specific rule (Send never overdraws, Open is unclaimed, etc.).
ValidateBlock(node, b) ==
  /\ b \in Received[node]
  /\ \E pk \in PublicKey : b.sig = pk /\ pk = b.acct
  /\ \E n \in Node : Ledger[n][b.prev] # NoBlockVal \/ b.prev = NoHash
  /\ \/ /\ b.tag = "send"
        /\ SenderBalance(b.acct, node) >= 1
     \/ /\ b.tag \in {"open", "receive"}
        /\ \E h \in Hash : \E m \in Node :
             /\ Ledger[m][h].tag = "send" /\ Ledger[m][h].acct = b.acct
             /\ Ledger[m][h] \notin Received[node]
     \/ /\ b.tag \in {"open", "receive"}
        /\ SenderBalance(b.acct, node) = 0
     \/ /\ b.tag = "change"
        /\ SenderBalance(b.acct, node) > 0
  /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![b.hash] = b]]
  /\ Received' = [n \in Node |-> IF n = node THEN Received[n] \ {b} ELSE Received[n]]
  /\ LastHash' = LastHash

Next ==
  \/ \E creator \in PrivateKey : CreateGenesisBlock(creator)
  \/ \E node \in Node, sender \in PublicKey, recipient \in PublicKey, k \in 1..GenesisBalance : CreateSendBlock(node, sender, recipient, k)
  \/ \E node \in Node, recipient \in PublicKey : CreateOpenBlock(node, recipient)
  \/ \E node \in Node, receiver \in PublicKey, sender \in PublicKey : CreateReceiveBlock(node, receiver, sender)
  \/ \E node \in Node, acct \in PublicKey : CreateChangeRepBlock(node, acct)
  \/ \E node \in Node, b \in Block : ValidateBlock(node, b)

Spec == Init /\ [][Next]_vars

\* Signatures are correct and every block in every replica's ledger is
\* accounted for: no block ever appears in the replicated ledger without a
\* genuine signature from the account it belongs to.
SafetyInvariant ==
  /\ TypeOK
  /\ \A n \in Node, h \in Hash : Ledger[n][h] # NoBlockVal => \E pk \in PublicKey : Ledger[n][h].sig = pk /\ pk = Ledger[n][h].acct
====