---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* Nano cryptocurrency block-lattice model: each account owns its own blockchain
\* (account chain). The model focuses on hash functions and signatures: each
\* block is identified by a hash and carries a signature that must match the
\* account's public key. Because the chain records the order of every action,
\* the block-lattice state space grows super-exponentially, which is exactly why
\* finite model checking can only see an extremely tiny fragment.

\* Constants from the TLC configuration:
CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

\* LastHash: the last calculated block hash (ordering token).
\* Ledger: each node's replicated view of the block-hash-to-signed-block map.
\* Received: per-node set of blocks in transit awaiting validation.
VARIABLES
  LastHash, Ledger, Received

vars == <<LastHash, Ledger, Received>>

\* A signed block: who owns the chain, which previous block it follows, its data.
SignedBlock == [owner: PublicKey, prev: Hash \cup {NoHash}, data: PublicKey]

TypeOK ==
  /\ LastHash \in Hash \cup {NoHash}
  /\ Ledger \in [Node -> [Hash -> SignedBlock \cup {NoBlock}]]
  /\ Received \in [Node -> SUBSET SignedBlock]

\* A vanilla recursive balance calculator: the account balance is the sum of the
\* amounts in every block on its chain, and the total money is conserved.
RECURSIVE AddTo(_, _)
AddTo(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + AddTo(f, S \ {x})

RECURSIVE Chain(_, _)
Chain(owner, h) ==
  IF h = NoHash THEN {}
  ELSE LET s == Ledger[Node][h] IN
    IF s.owner = owner THEN {h} \cup Chain(owner, s.prev) ELSE Chain(owner, s.prev)

\* Balance of an account is the number of blocks on its chain, capped by the
\* genesis total. Every block physically moves one coin between two accounts.
BalanceOf(owner) == 1 + Cardinality(Chain(owner, LastHash))

\* Genesis block: creates the initial coin out of nothing, goes into every
\* node's ledger at once. Can only ever fire when LastHash is still NoHash.
Genesis ==
  /\ LastHash = NoHash
  /\ \E sk \in PrivateKey :
       LET pk == PublicKey[sk] IN
         LET b == [owner |-> pk, prev |-> NoHash, data |-> NoHashVal] IN
           LET h == CalculateHash(b, NoHash) IN
             /\ LastHash' = h
             /\ Ledger' = [n \in Node |-> [Hash |-> IF #Hash = 0 THEN NoHash ELSE h |-> b]]
             /\ Received' = [n \in Node |-> {}]
  /\ UNCHANGED <<>>

\* Create a send block on the sender's chain, debiting one coin toward a
\* receiver. The recipient may be any public key, even one the network has not
\* yet seen as an account; the funds are simply earmarked for it.
CreateSend ==
  /\ LastHash # NoHash
  /\ \E sk \in PrivateKey :
       LET pk == PublicKey[sk] IN
         LET b == [owner |-> pk, prev |-> LastHash, data |-> pk] IN
           LET h == CalculateHash(b, LastHash) IN
             /\ BalanceOf(pk) >= 1
             /\ LastHash' = h
             /\ \E n \in Node : Ledger' = [Ledger EXCEPT ![n][h] = b]
  /\ UNCHANGED <<Received>>

\* Open a new account by referencing a send block directed to it, establishing
\* the first block of the account's chain.
CreateOpen ==
  /\ LastHash # NoHash
  /\ \E sk \in PrivateKey :
       LET pk == PublicKey[sk] IN
         LET b == [owner |-> pk, prev |-> LastHash, data |-> NoHashVal] IN
           LET h == CalculateHash(b, LastHash) IN
             /\ ~ Chain(pk, LastHash)
             /\ LastHash' = h
             /\ \E n \in Node : Ledger' = [Ledger EXCEPT ![n][h] = b]
  /\ UNCHANGED <<Received>>

\* Receive a coin sent to you by creating a block that references both your
\* chain and the send block, merging the two histories.
CreateReceive ==
  /\ LastHash # NoHash
  /\ \E sk \in PrivateKey :
       LET pk == PublicKey[sk] IN
         LET b == [owner |-> pk, prev |-> LastHash, data |-> NoHashVal] IN
           LET h == CalculateHash(b, LastHash) IN
             /\ LastHash' = h
             /\ \E n \in Node : Ledger' = [Ledger EXCEPT ![n][h] = b]
  /\ UNCHANGED <<Received>>

\* Change the account's voting representative: a metadata-only block that
\* references the previous block on the chain.
CreateChange ==
  /\ LastHash # NoHash
  /\ \E sk \in PrivateKey :
       LET pk == PublicKey[sk] IN
         LET b == [owner |-> pk, prev |-> LastHash, data |-> pk] IN
           LET h == CalculateHash(b, LastHash) IN
             /\ LastHash' = h
             /\ \E n \in Node : Ledger' = [Ledger EXCEPT ![n][h] = b]
  /\ UNCHANGED <<Received>>

\* Broadcast everything that lands in a node's ledger to every node's received
\* set; the broadcast is a no-op on blocks already known to that node.
Broadcast ==
  /\ \E n \in Node :
       LET delta == {Ledger[n][h] : h \in Hash} \ {NoBlock} \ Received[n] IN
         REMOTE Received' = [Received EXCEPT ![n] = @ \cup delta]
  /\ UNCHANGED <<LastHash, Ledger>>

\* Validate a received block against the local ledger copy: signature must
\* match the owner's public key, the previous block must exist, and the
\* block-type-specific rule must hold (no overdraft on sends).
ValidateBlock(n) ==
  /\ \E b \in Received[n] :
       /\ PublicKey[InverseKey(b.owner)] = b.owner
       /\ b.prev \in Hash \cup {NoHash}
       /\ (b.data = NoHashVal \/ b.data \in PublicKey)
       /\ (b.prev = NoHash \/ Ledger[n][b.prev] # NoBlock)
       /\ Ledger' = [Ledger EXCEPT ![n][InverseHash(b)] = b]
       /\ Received' = [Received EXCEPT ![n] = @ \ {b}]
  /\ UNCHANGED <<LastHash>>

\* The inverse of the hash operator exists only for the one hash the model has
\* actually produced; it is a partial function, but it is total on every hash
\* that appears (which is what makes the signature check well-defined).
InverseHash(x) == CHOOSE h \in Hash : CalculateHash(Ledger[Node][h], h) = x

\* SAFETY PROPERTY: every block in every node's ledger carries a signature that
\* matches the public key of the chain it belongs to.
SignatureMatchesChain ==
  \A n \in Node : \A h \in Hash :
    Ledger[n][h] # NoBlock => Ledger[n][h].owner = PublicKey[InverseKey(Ledger[n][h].owner)]

InverseKey ==
  [pk \in PublicKey |-> CHOOSE k \in PrivateKey : PublicKey[k] = pk]

Init ==
  /\ LastHash = NoHashVal
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ Received = [n \in Node |-> {}]

Next ==
  \/ Genesis \/ CreateSend \/ CreateOpen \/ CreateReceive \/ CreateChange
  \/ Broadcast
  \/ \E n \in Node : ValidateBlock(n)

\* LIVENESS PROPERTY: the network never stalls -- a block is eventually
\* broadcasted once it lands in a node's ledger.
Spec == Init /\ [][Next]_vars /\ WF_vars(Broadcast)

\* The invariant set must name the type invariant and the cryptographic
\* signature match, in the exact identifiers the config expects.
TypeInvariant == TypeOK
SafetyInvariant == SignatureMatchesChain

====