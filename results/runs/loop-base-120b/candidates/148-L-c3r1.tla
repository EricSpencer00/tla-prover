---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(*  CONSTANTS                                                            *)
(***************************************************************************)

CONSTANTS
    Hash,                \* Set of all possible block hashes
    NoHashVal,           \* Sentinel value meaning “no hash yet”
    PrivateKey,          \* Set of private keys
    PublicKey,           \* Set of public keys
    Node,                \* Set of network nodes
    GenesisBalance,      \* Total supply of Nano at genesis (a natural number)
    NoBlockVal,          \* Sentinel value meaning “no block stored”
    CalculateHash        \* Abstract hash operator (will be overridden by CalculateHashImpl)

\*-----------------------------------------------------------------------
\*  Derived constants / helper mappings (must be provided by the .cfg)
\*-----------------------------------------------------------------------
\* Mapping from a private key to its public key
ASSUME PrivToPub \in [PrivateKey -> PublicKey]

\* Mapping from each node to the private key it owns
ASSUME NodeKey \in [Node -> PrivateKey]

\* Aliases for readability
NoHash == NoHashVal
NoBlock == NoBlockVal

\*-----------------------------------------------------------------------
\*  Block definition
\*-----------------------------------------------------------------------
Block ==
    [ type        : {"Genesis", "Send", "Open", "Receive", "Change"},
      prevHash    : Hash \/ {NoHashVal},
      account     : PublicKey,
      signature   : PrivateKey,               \* For simplicity the “signature” is just the private key
      amount      : Nat,
      recipient   : PublicKey,
      sourceHash  : Hash \/ {NoHashVal},      \* For Open/Receive blocks: the hash of the send block they consume
      rep         : PublicKey                 \* For Change blocks: new representative
    ]

\* The universe of stored block values (either a real block or the sentinel)
BlockOrNone == Block \/ {NoBlockVal}

\*-----------------------------------------------------------------------
\*  Variables
\*-----------------------------------------------------------------------
VARIABLES
    LastHash,   \* The hash of the most recently created block (or NoHashVal)
    Ledgers,    \* Per‑node copy of the distributed ledger
    Received    \* Per‑node set of hashes that have been received but not yet processed

\* Ledger is a function from a node to a function from a hash to a block (or NoBlock)
LedgerType == [Node -> [Hash -> BlockOrNone]]

\*-----------------------------------------------------------------------
\*  Helper operators
\*-----------------------------------------------------------------------

\* Alias for the hash function used throughout the spec
CalcHash(data, prev) == CalculateHashImpl(data, prev)

\* The concrete implementation of CalculateHash that the .cfg will substitute
CalculateHashImpl(data, prev) == CalculateHash(data, prev)

\* Retrieve the public key that owns a given node
NodePubKey(n) == PrivToPub[NodeKey[n]]

\* Check whether a signature stored in a block is valid.
\* In this abstract model the signature is just the private key that signed the block.
ValidSignature(b) ==
    /\ b.signature \in PrivateKey
    /\ PrivToPub[b.signature] = b.account

\* Determine the previous hash for a given account chain.
\* If the account has no blocks yet, the predecessor is NoHashVal.
PrevHashForAccount(pub) ==
    LET hSet == { h \in Hash :
                    \E n \in Node :
                        Ledgers[n][h] # NoBlockVal /\ Ledgers[n][h].account = pub }
    IN IF hSet = {} THEN NoHashVal ELSE Max(hSet)

\* Compute the balance of an account by walking its chain.
Balance(pub) ==
    LET chain ==
        { h \in Hash :
            \E n \in Node :
                Ledgers[n][h] # NoBlockVal /\ Ledgers[n][h].account = pub }
    IN IF chain = {} THEN 0
       ELSE
           LET last == Max(chain) IN
           BalanceFromHash(pub, last)

\* Helper that recursively computes balance from a given hash of the account chain.
BalanceFromHash(pub, h) ==
    LET blk == CHOOSE b \in Block :
                \E n \in Node : Ledgers[n][h] = b
    IN CASE blk.type = "Genesis" -> blk.amount
        [] blk.type = "Send"    -> BalanceFromHash(pub, blk.prevHash) - blk.amount
        [] blk.type = "Open"    -> blk.amount
        [] blk.type = "Receive" -> BalanceFromHash(pub, blk.prevHash) + blk.amount
        [] blk.type = "Change"  -> BalanceFromHash(pub, blk.prevHash)
        [] OTHER               -> 0

\* Predicate ensuring that a newly created block respects type‑specific rules.
BlockWellFormed(b) ==
    /\ b.account \in PublicKey
    /\ b.signature \in PrivateKey
    /\ ValidSignature(b)
    /\ CASE b.type = "Genesis"   ->
            /\ b.prevHash = NoHashVal
            /\ b.amount = GenesisBalance
            /\ b.recipient = b.account
            /\ b.sourceHash = NoHashVal
            /\ b.rep = b.account
       [] b.type = "Send"      ->
            /\ b.prevHash \in Hash
            /\ b.amount \in Nat
            /\ b.recipient \in PublicKey
            /\ b.sourceHash = NoHashVal
            /\ b.rep = b.account
            /\ b.amount <= Balance(b.account)
       [] b.type = "Open"      ->
            /\ b.prevHash = NoHashVal
            /\ b.amount \in Nat
            /\ b.recipient = b.account
            /\ b.sourceHash \in Hash
            /\ b.rep = b.account
            /\ \E senderPub \in PublicKey :
                  \E sndBlk \in Block :
                      /\ sndBlk.type = "Send"
                      /\ sndBlk.recipient = b.account
                      /\ sndBlk.amount = b.amount
                      /\ sndBlk.account = senderPub
                      /\ sndBlk.prevHash = b.sourceHash
       [] b.type = "Receive"   ->
            /\ b.prevHash \in Hash
            /\ b.amount \in Nat
            /\ b.recipient = b.account
            /\ b.sourceHash \in Hash
            /\ b.rep = b.account
            /\ \E sndBlk \in Block :
                  /\ sndBlk.type = "Send"
                  /\ sndBlk.recipient = b.account
                  /\ sndBlk.amount = b.amount
                  /\ sndBlk.account # b.account
                  /\ sndBlk.prevHash = b.sourceHash
       [] b.type = "Change"    ->
            /\ b.prevHash \in Hash
            /\ b.amount = 0
            /\ b.recipient = b.account
            /\ b.sourceHash = NoHashVal
            /\ b.rep \in PublicKey

\*-----------------------------------------------------------------------
\*  Initial state
\*-----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHashVal
    /\ Ledgers = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]

\*-----------------------------------------------------------------------
\*  Actions
\*-----------------------------------------------------------------------

\* 1. Create the genesis block (can happen only once)
CreateGenesis ==
    /\ LastHash = NoHashVal
    /\ \E creator \in Node :
          LET pub == NodePubKey(creator) IN
          LET blk == [ type        |-> "Genesis",
                       prevHash    |-> NoHashVal,
                       account     |-> pub,
                       signature   |-> NodeKey(creator),
                       amount      |-> GenesisBalance,
                       recipient   |-> pub,
                       sourceHash  |-> NoHashVal,
                       rep         |-> pub ] IN
          /\ BlockWellFormed(blk)
          LET h == CalcHash(blk, NoHashVal) IN
               /\ h \in Hash
               /\ LastHash' = h
               /\ Ledgers' = [n \in Node |
                                 [h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledgers[n][h2]]]
               /\ Received' = [n \in Node |-> {}]

\* 2. Create a Send block
CreateSend ==
    /\ LastHash # NoHashVal
    /\ \E creator \in Node :
          LET senderPub == NodePubKey(creator) IN
          LET prevH == PrevHashForAccount(senderPub) IN
          LET maxAmt == Balance(senderPub) IN
          /\ maxAmt > 0
          \* Choose a positive amount not exceeding balance
          \E amt \in Nat :
                /\ amt > 0 /\ amt <= maxAmt
                \E rcptPub \in PublicKey :
                      LET blk == [ type        |-> "Send",
                                   prevHash    |-> prevH,
                                   account     |-> senderPub,
                                   signature   |-> NodeKey(creator),
                                   amount      |-> amt,
                                   recipient   |-> rcptPub,
                                   sourceHash  |-> NoHashVal,
                                   rep         |-> senderPub ] IN
                      /\ BlockWellFormed(blk)
                      LET h == CalcHash(blk, prevH) IN
                           /\ h \in Hash
                           /\ LastHash' = h
                           /\ Ledgers' = [n \in Node |
                                            [h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledgers[n][h2]]]
                           /\ Received' = [n \in Node |-> Received[n] \cup {h}]

\* 3. Create an Open block (opening a new account)
CreateOpen ==
    /\ LastHash # NoHashVal
    /\ \E creator \in Node :
          LET newPub == NodePubKey(creator) IN
          \E srcHash \in Hash :
                \E sndBlk \in Block :
                      /\ sndBlk.type = "Send"
                      /\ sndBlk.recipient = newPub
                      /\ sndBlk.prevHash = srcHash
                      LET blk == [ type        |-> "Open",
                                   prevHash    |-> NoHashVal,
                                   account     |-> newPub,
                                   signature   |-> NodeKey(creator),
                                   amount      |-> sndBlk.amount,
                                   recipient   |-> newPub,
                                   sourceHash  |-> srcHash,
                                   rep         |-> newPub ] IN
                      /\ BlockWellFormed(blk)
                      LET h == CalcHash(blk, NoHashVal) IN
                           /\ h \in Hash
                           /\ LastHash' = h
                           /\ Ledgers' = [n \in Node |
                                            [h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledgers[n][h2]]]
                           /\ Received' = [n \in Node |-> Received[n] \cup {h}]

\* 4. Create a Receive block
CreateReceive ==
    /\ LastHash # NoHashVal
    /\ \E creator \in Node :
          LET recvPub == NodePubKey(creator) IN
          LET prevH == PrevHashForAccount(recvPub) IN
          \E srcHash \in Hash :
                \E sndBlk \in Block :
                      /\ sndBlk.type = "Send"
                      /\ sndBlk.recipient = recvPub
                      /\ sndBlk.prevHash = srcHash
                      LET blk == [ type        |-> "Receive",
                                   prevHash    |-> prevH,
                                   account     |-> recvPub,
                                   signature   |-> NodeKey(creator),
                                   amount      |-> sndBlk.amount,
                                   recipient   |-> recvPub,
                                   sourceHash  |-> srcHash,
                                   rep         |-> recvPub ] IN
                      /\ BlockWellFormed(blk)
                      LET h == CalcHash(blk, prevH) IN
                           /\ h \in Hash
                           /\ LastHash' = h
                           /\ Ledgers' = [n \in Node |
                                            [h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledgers[n][h2]]]
                           /\ Received' = [n \in Node |-> Received[n] \cup {h}]

\* 5. Create a Change Representative block
CreateChange ==
    /\ LastHash # NoHashVal
    /\ \E creator \in Node :
          LET acctPub == NodePubKey(creator) IN
          LET prevH == PrevHashForAccount(acctPub) IN
          \E newRep \in PublicKey :
                LET blk == [ type        |-> "Change",
                             prevHash    |-> prevH,
                             account     |-> acctPub,
                             signature   |-> NodeKey(creator),
                             amount      |-> 0,
                             recipient   |-> acctPub,
                             sourceHash  |-> NoHashVal,
                             rep         |-> newRep ] IN
                /\ BlockWellFormed(blk)
                LET h == CalcHash(blk, prevH) IN
                     /\ h \in Hash
                     /\ LastHash' = h
                     /\ Ledgers' = [n \in Node |
                                      [h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledgers[n][h2]]]
                     /\ Received' = [n \in Node |-> Received[n] \cup {h}]

\* 6. Process a received block at a node
ProcessBlock ==
    /\ \E n \in Node :
          /\ Received[n] # {}
          /\ \E h \in Received[n] :
                /\ Ledgers[n][h] = NoBlockVal
                /\ \E blk \in Block :
                       /\ blk = CHOOSE b \in Block : CalcHash(b, b.prevHash) = h
                       /\ BlockWellFormed(blk)
                       /\ (blk.prevHash = NoHashVal \/ Ledgers[n][blk.prevHash] # NoBlockVal)
                /\ Ledgers' = [m \in Node |
                                 IF m = n
                                 THEN [h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledgers[m][h2]]
                                 ELSE Ledgers[m]]
                /\ Received' = [m \in Node |
                                 IF m = n
                                 THEN Received[m] \ {h}
                                 ELSE Received[m]]
                /\ UNCHANGED LastHash
    /\ UNCHANGED << >>

\*-----------------------------------------------------------------------
\*  Next-state relation
\*-----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\*-----------------------------------------------------------------------
\*  Specification
\*-----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<LastHash, Ledgers, Received>>

\*-----------------------------------------------------------------------
\*  Type invariant
\*-----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash \/ {NoHashVal}
    /\ Ledgers \in LedgerType
    /\ Received \in [Node -> SUBSET Hash]
    /\ \A n \in Node: \A h \in Hash:
          (Ledgers[n][h] # NoBlockVal) => Ledgers[n][h] \in Block
    /\ \A n \in Node: \A h \in Received[n]: h \in Hash

\*-----------------------------------------------------------------------
\*  Safety invariant (cryptographic correctness)
\*-----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node: \A h \in Hash:
        (Ledgers[n][h] # NoBlockVal) => ValidSignature(Ledgers[n][h])

\*-----------------------------------------------------------------------
\*  THE END
\*-----------------------------------------------------------------------
====