---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash
CONSTANTS CalculateHashImpl

\* Hash: the finite set of block hashes the model may produce.
\* NoHashVal: the sentinel hash for "no previous block" / "no block yet".
\* PrivateKey/PublicKey: the node key pairs; PublicOf links a private key to its public key.
\* Node: the network nodes; GenesisBalance: the total coin supply.
\* NoBlockVal: the sentinel block that marks an empty slot in a node's ledger.
\* NoHash: the sentinel hash for an empty received set, avoiding a duplicate hash value.
\* CalculateHashImpl: the model's bounded hash operator, substituted for CalculateHash in the .cfg.

PublicOf : [PrivateKey -> PublicKey]

\* A signed block; Chain identifies the owning account's chain, Prev the previous block in it.
\* Signer is the private key that signed this block; Amount is the amount moved (0 for non-send).
\* Target is the recipient of a send block (and the other leg of a receive block); Type chooses the block kind.
SignedBlock : {NoBlockVal} \cup [Chain: PublicKey, Prev: {NoHashVal} \cup Hash, Signer: PrivateKey,
                                   Amount: 0..GenesisBalance, Target: PublicKey, Type: {"send", "open", "receive", "change"}]

VARIABLES LastHash, Ledger, Received
vars == <<LastHash, Ledger, Received>>

\* The last calculated hash; replicated ledger per node mapping a hash to a signed block or NoBlockVal;
\* a per-node set of received-but-not-yet-validated blocks (each block carries its hash).
TypeInvariant ==
  /\ LastHash \in {NoHashVal} \cup Hash
  /\ Ledger \in [Node -> [Hash -> SignedBlock]]
  /\ Received \in [Node -> SUBSET SignedBlock]

\* Sum of all account balances must never exceed the genesis balance; the chain holds every spend.
RECURSIVE SumBalances(_)
SumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE e \in S : TRUE IN AccountBalance(x) + SumBalances(S \ {x})

\* AccountBalance walks an account chain to compute the current balance of a public key.
RECURSIVE AccountBalance(_)
AccountBalance(pub) ==
  LET lastBlock == CHOOSE h \in {h \in Hash : \E n \in Node : Ledger[n][h] # NoBlockVal /\ Ledger[n][h].Chain = pub} : TRUE
      b == \E n \in Node : Ledger[n][lastBlock]
  IN IF \A n \in Node : Ledger[n][lastBlock] = NoBlockVal THEN 0
     ELSE IF b.Type = "send" THEN AccountBalance(pub) - b.Amount
          ELSE IF b.Type = "receive" THEN AccountBalance(pub) + b.Amount
               ELSE AccountBalance(pub)

Init ==
  /\ LastHash = NoHashVal
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ Received = [n \in Node |-> {}]

\* Genesis block: initializes the chain with the whole supply, added to every node's ledger at once.
CreateGenesisBlock(k) ==
  /\ LastHash = NoHashVal
  /\ \A n \in Node : Ledger[n][NoHashVal] = NoBlockVal
  /\ LET h == CalculateHashImpl(k, NoHashVal) IN
       /\ LastHash' = h
       /\ Ledger' = [n \in Node |-> [h |-> [Chain |-> PublicOf[k], Prev |-> NoHashVal,
                                          Signer |-> k, Amount |-> GenesisBalance,
                                          Target |-> PublicOf[k], Type |-> "open"], NoHashVal |-> NoBlockVal]]
       /\ Received' = [n \in Node |-> {}]

\* Send block: debits the sender's account and names a recipient.
CreateSendBlock(k, to) ==
  /\ LastHash # NoHashVal
  /\ LET bal == AccountBalance(PublicOf[k]) IN \E amt \in 1..bal :
       LET h == CalculateHashImpl(k, LastHash) IN
         /\ LastHash' = h
         /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = [Chain |-> PublicOf[k], Prev |-> LastHash,
                                    Signer |-> k, Amount |-> amt, Target |-> to, Type |-> "send"], NoHashVal |-> NoBlockVal]]
         /\ Received' = [n \in Node |-> Received[n] \cup {[Chain |-> PublicOf[k], Prev |-> LastHash,
                                    Signer |-> k, Amount |-> amt, Target |-> to, Type |-> "send"]}]

\* Open block: first block for a new account, pointing at a send addressed to it.
CreateOpenBlock(k, parent) ==
  /\ \E s \in SentBlocks : s.Signer = parent /\ s.Target = PublicOf[k]
  /\ LET h == CalculateHashImpl(k, NoHashVal) IN
       /\ LastHash' = h
       /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = [Chain |-> PublicOf[k], Prev |-> NoHashVal,
                                  Signer |-> k, Amount |-> 0, Target |-> PublicOf[k], Type |-> "open"], NoHashVal |-> NoBlockVal]]
       /\ Received' = [n \in Node |-> Received[n] \cup {[Chain |-> PublicOf[k], Prev |-> NoHashVal,
                                  Signer |-> k, Amount |-> 0, Target |-> PublicOf[k], Type |-> "open"]}]

\* Receive block: claims a pending send into the receiver's account.
CreateReceiveBlock(k, parent, source) ==
  /\ \E s \in SentBlocks : s.Signer = source /\ s.Target = PublicOf[k]
  /\ LET h == CalculateHashImpl(k, parent) IN
       /\ LastHash' = h
       /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = [Chain |-> PublicOf[k], Prev |-> parent,
                                  Signer |-> k, Amount |-> 0, Target |-> PublicOf[source], Type |-> "receive"], NoHashVal |-> NoBlockVal]]
       /\ Received' = [n \in Node |-> Received[n] \cup {[Chain |-> PublicOf[k], Prev |-> parent,
                                  Signer |-> k, Amount |-> 0, Target |-> PublicOf[source], Type |-> "receive"]}]

\* Change-representative block: rotates the voting key, ordinary block with no monetary effect.
CreateChangeBlock(k, parent) ==
  /\ LastHash # NoHashVal
  /\ LET h == CalculateHashImpl(k, parent) IN
       /\ LastHash' = h
       /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = [Chain |-> PublicOf[k], Prev |-> parent,
                                  Signer |-> k, Amount |-> 0, Target |-> PublicOf[k], Type |-> "change"], NoHashVal |-> NoBlockVal]]
       /\ Received' = [n \in Node |-> Received[n] \cup {[Chain |-> PublicOf[k], Prev |-> parent,
                                  Signer |-> k, Amount |-> 0, Target |-> PublicOf[k], Type |-> "change"]}]

\* Validation accepts a received block into the ledger after signature and balance checking.
ValidateBlock(n, b) ==
  /\ b \in Received[n]
  /\ LET own == Ledger[n][CalculateHashImpl(b.Signer, b.Prev)] IN
       /\ own = NoBlockVal
       /\ PublicOf[b.Signer] = Ledger[n][CalculateHashImpl(b.Signer, b.Prev)].Chain
       /\ (b.Type # "send" \/ b.Amount <= AccountBalance(PublicOf[b.Signer]))
       /\ Ledger' = [Ledger EXCEPT ![n] = [Ledger[n] EXCEPT ![CalculateHashImpl(b.Signer, b.Prev)] = b]]
       /\ Received' = [Received EXCEPT ![n] = Received[n] \ {b}]
       /\ UNCHANGED LastHash

Next ==
  \/ \E k \in PrivateKey : CreateGenesisBlock(k) \/ CreateChangeBlock(k, LastHash)
  \/ \E k \in PrivateKey, to \in PublicKey : CreateSendBlock(k, to)
  \/ \E k \in PrivateKey, v \in {NoHashVal} \cup Hash : CreateOpenBlock(k, v) \/ CreateReceiveBlock(k, v, v)
  \/ \E n \in Node, b \in SignedBlock : ValidateBlock(n, b)

Spec == Init /\ [][Next]_vars

\* SafetyInvariant: every block in every node's ledger has a signature matching its chain's public key.
SafetyInvariant ==
  \A n \in Node, h \in Hash : Ledger[n][h] # NoBlockVal => PublicOf[Ledger[n][h].Signer] = Ledger[n][h].Chain

SentBlocks == {b \in SignedBlock : b.Type = "send"}

====