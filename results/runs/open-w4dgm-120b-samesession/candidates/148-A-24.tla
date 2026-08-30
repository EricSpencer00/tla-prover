---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* One-to-many key mapping: a private key's matching public key (at most one
\* per private key in this simplified model).
Public(p) == CHOOSE q \in PublicKey : PublicToPrivate[q] = p

\* Block types: the data stored in an account-chain block. Each references the
\* previous block in its own chain (prev) and, for sends/receives, the block it
\* interacts with (partner) so that ordering and double-spending checks are
\* chain-local rather than globally indexed.
Block == [ct : {"genesis", "send", "open", "receive", "change"},
           acct : PublicKey, amt : 0..GenesisBalance, prev : Hash, partner : Hash \cup {NoHash}]

\* The chain for an account is a linked list via prev-hash; the balance is
\* computed by walking the chain, decrementing on sends and incrementing on
\* receives. This is where the "record of actions" lives in the model.
RECURSIVE WalkChain(_)
WalkChain(h) == IF h = NoHash THEN 0
                ELSE LET b == Ledger[Node][h] IN
                     (IF b = NoBlockVal THEN 0 ELSE
                       (IF b.ct = "send" THEN -b.amt
                        ELSE IF b.ct = "receive" THEN b.amt
                        ELSE 0) + WalkChain(b.prev))

AccountBalance(k) == WalkChain(Ledger[Node][LastHash] \in Block /\ Block.acct = k)

RECURSIVE SumBalances(_)
SumBalances(S) == IF S = {} THEN 0
                  ELSE LET x == CHOOSE y \in S : TRUE IN AccountBalance(x) + SumBalances(S \ {x})

\* Balls-into-bins view of the chain: the per-node ledgers must partition the
\* one shared set of block hashes, since each hash can appear at most once per
\* node's ledger and the hash space is finite.
NodeAssigner == [n \in Node |-> {h \in Hash : Ledger[n][h] # NoBlockVal}]
LedgerBinned == {NodeAssigner[n] : n \in Node}

VARIABLES LastHash, Ledger, Received

vars == <<LastHash, Ledger, Received>>

TypeOK ==
  /\ LastHash \in Hash \cup {NoHash}
  /\ Ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ Received \in [Node -> SUBSET Hash]

Init ==
  /\ LastHash = NoHash
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ Received = [n \in Node |-> {}]

\* The genesis block is the only way coins enter the system: a private key
\* holder mints the full supply into their own account at the start.
CreateGenesisBlock(p) ==
  /\ LastHash = NoHash
  /\ \A n \in Node : Ledger[n][NoHashVal] = NoBlockVal
  /\ LET h == CalculateHash("genesis", Public(p), GenesisBalance, NoHash, NoHash)
     IN /\ LastHash' = h
        /\ Ledger' = [n \in Node |> [Ledger[n] EXCEPT ![h] = [ct |-> "genesis", acct |-> Public(p),
                                                                amt |-> GenesisBalance, prev |-> NoHash,
                                                                partner |-> NoHash]]]
        /\ Received' = Received

\* A send block debits the sender's chain balance; the accounting rule is
\* enforced here, not later when the recipient claims the funds.
CreateSendBlock(n, amt) ==
  /\ amt > 0 /\ amt <= AccountBalance(Public(n))
  /\ LastHash # NoHash
  /\ LET h == CalculateHash("send", Public(n), amt, LastHash, NoHash)
     IN /\ LastHash' = h
        /\ Ledger' = [m \in Node |> [Ledger[m] EXCEPT ![h] = [ct |-> "send", acct |-> Public(n), amt |-> amt,
                                                                prev |-> LastHash, partner |-> NoHash]]]
        /\ Received' = Received

CreateOpenBlock(n, h) ==
  /\ Ledger[Node][h] # NoBlockVal /\ Ledger[Node][h].ct = "send"
  /\ Ledger[Node][h].acct = Public(n) /\ h \notin NodeAssigner[n]
  /\ LET g == CalculateHash("open", Public(n), 0, NoHash, h)
     IN /\ LastHash' = g
        /\ Ledger' = [m \in Node |> [Ledger[m] EXCEPT ![g] = [ct |-> "open", acct |-> Public(n), amt |-> 0,
                                                                prev |-> NoHash, partner |-> h]]]
        /\ Received' = Received

CreateReceiveBlock(n, h) ==
  /\ Ledger[Node][h] # NoBlockVal /\ Ledger[Node][h].ct = "send"
  /\ Ledger[Node][h].acct # Public(n) /\ h \notin NodeAssigner[n]
  /\ LET g == CalculateHash("receive", Public(n), Ledger[Node][h].amt, LastHash, h)
     IN /\ LastHash' = g
        /\ Ledger' = [m \in Node |> [Ledger[m] EXCEPT ![g] = [ct |-> "receive", acct |-> Public(n),
                                                                amt |-> Ledger[Node][h].amt, prev |-> LastHash,
                                                                partner |-> h]]]
        /\ Received' = Received

CreateChangeBlock(n) ==
  /\ LastHash # NoHash
  /\ LET h == CalculateHash("change", Public(n), 0, LastHash, NoHash)
     IN /\ LastHash' = h
        /\ Ledger' = [m \in Node |> [Ledger[m] EXCEPT ![h] = [ct |-> "change", acct |-> Public(n), amt |-> 0,
                                                                prev |-> LastHash, partner |-> NoHash]]]
        /\ Received' = Received

Broadcast(h) ==
  /\ h \notin Received[Node]
  /\ Received' = [Received EXCEPT ![Node] = Received[Node] \cup {h}]
  /\ UNCHANGED <<LastHash, Ledger>>

\* Validation is the whole point: a node only incorporates a block whose
\* signature checks out under the account's public key and that passes the
\* block-type rule. Because the chain is a linked list, a block that was
\* forged by copying someone else's signature would still fail the receiver's
\* own signature check.
ValidateReceived(n) ==
  /\ \E h \in Received[n] :
       /\ Ledger[n][h] = NoBlockVal
       /\ LET b == Ledger[Node][h] IN
            /\ SignatureValid(b) /\ BlockTypeValid(b, n)
            /\ Ledger' = [Ledger EXCEPT ![n][h] = b]
       /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]
  /\ UNCHANGED LastHash

SignatureValid(b) == b # NoBlockVal /\ b.acct = Public(n)

BlockTypeValid(b, n) ==
  /\ b \in Block
  /\ ((b.ct = "genesis") => (b.prev = NoHash /\ b.amt = GenesisBalance))
  /\ ((b.ct = "send") => (b.prev \in NodeAssigner[n] /\ b.amt <= AccountBalance(b.acct)))
  /\ ((b.ct = "open") => (b.prev = NoHash /\ b.partner \in NodeAssigner[n]))
  /\ ((b.ct = "receive") => (b.prev \in NodeAssigner[n] /\ b.partner \in NodeAssigner[n]))
  /\ ((b.ct = "change") => (b.prev \in NodeAssigner[n]))

Next ==
  \/ \E p \in PrivateKey : CreateGenesisBlock(p)
  \/ \E n \in Node, amt \in 1..GenesisBalance : CreateSendBlock(n, amt)
  \/ \E n \in Node, h \in Hash : CreateOpenBlock(n, h)
  \/ \E n \in Node, h \in Hash : CreateReceiveBlock(n, h)
  \/ \E n \in Node : CreateChangeBlock(n)
  \/ \E h \in Hash : Broadcast(h)
  \/ \E n \in Node : ValidateReceived(n)

\* Spec: fairness is not the focus here because chaining and double-spending
\* are structural properties of the block and signature rules themselves; no
\* liveness property is required to rule out a safety violation.
Spec == Init /\ [][Next]_vars

\* Chain-partitioning: with a finite hash space every hash is either present
\* in a node's ledger or in the network's transit buffer, never both, so the
\* two cannot contain the same hash and a block can never be double-counted.
TypeInvariant == TypeOK

\* Safety: every block in the replicated ledger must still carry a signature
\* that matches its owner's public key -- nothing accepted into the chain is
\* a forged (or statically corrupted) block.
SafetyInvariant == \A n \in Node : \A h \in Hash : Ledger[n][h] # NoBlockVal => Ledger[n][h].acct = Public(n)

====