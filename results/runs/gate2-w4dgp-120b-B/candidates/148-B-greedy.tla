---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,                   \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* An action calculating the hash of a block
    PrivateKey,             \* The set of all Ed25519 private keys
    PublicKey,              \* The set of all Ed25519 public keys
    KeyPair,                \* The public key paired with each private key
    Node,                   \* The set of all nodes in the network
    GenesisBalance,         \* The total number of coins in the network
    Ownership               \* The private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash :
        /\ CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

\* Functions to sign hashes with private key and validate signatures against
\* public key.
SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature == [data : Hash, signedWith : PrivateKey]

\* The set of protocol-conforming blocks.
AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type |-> "genesis", account |-> PublicKey, balance |-> {GenesisBalance}]

SendBlock ==
    [previous |-> Hash, balance |-> AccountBalance, destination |-> PublicKey,
     type |-> "send"]

OpenBlock ==
    [account |-> PublicKey, source |-> Hash, rep |-> PublicKey, type |-> "open"]

ReceiveBlock ==
    [previous |-> Hash, source |-> Hash, type |-> "receive"]

ChangeRepBlock ==
    [previous |-> Hash, rep |-> PublicKey, type |-> "change"]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock
         \cup ChangeRepBlock

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b \in SignedBlock : FALSE
NoHash == CHOOSE h \in Hash : FALSE

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

GenesisBlockExists == lastHash # NoHash

IsAccountOpen(ledger, publicKey) ==
    /\ \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock # NoBlock
        /\ signedBlock.block.type \in {"genesis", "open"}
        /\ signedBlock.block.account = publicKey

IsSendReceived(ledger, sourceHash) ==
    /\ \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock # NoBlock
        /\ signedBlock.block.type \in {"open", "receive"}
        /\ signedBlock.block.source = sourceHash

\* Recursive helper to find the account a block belongs to.
RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, blockHash) ==
    LET signedBlock == ledger[blockHash] IN
    IF signedBlock.block.type \in {"genesis", "open"}
    THEN signedBlock.block.account
    ELSE PublicKeyOf(ledger, signedBlock.block.previous)

TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock # NoBlock
        /\ PublicKeyOf(ledger, hash) = publicKey
        /\ ~\E otherHash \in Hash :
            LET otherSignedBlock == ledger[otherHash] IN
            /\ otherSignedBlock # NoBlock
            /\ otherSignedBlock.block.type \in {"send", "receive", "change"}
            /\ otherSignedBlock.block.previous = hash

\* Recursive helpers to compute an account's balance from its top block.
RECURSIVE BalanceAt(_,_)
RECURSIVE ValueOfSendBlock(_,_)

BalanceAt(ledger, hash) ==
    LET block == ledger[hash].block IN
    CASE block.type = "open" -> ValueOfSendBlock(ledger, block.source)
    [] block.type = "send" -> block.balance
    [] block.type = "receive" ->
        BalanceAt(ledger, block.previous) + ValueOfSendBlock(ledger, block.source)
    [] block.type = "change" -> BalanceAt(ledger, block.previous)
    [] block.type = "genesis" -> block.balance

ValueOfSendBlock(ledger, hash) ==
    LET block == ledger[hash].block IN
    BalanceAt(ledger, block.previous) - block.balance

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        /\ \A hash \in Hash :
            LET signedBlock == ledger[hash] IN
            signedBlock # NoBlock =>
                LET publicKey == PublicKeyOf(ledger, hash) IN
                ValidateSignature(signedBlock.signature, publicKey, hash)

\* Sum the balances of all open accounts in a node's ledger.
RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE LET e == CHOOSE x \in S : TRUE IN e + SumBag(B (-) SetToBag({e}))

BalanceInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        LET openAccounts == {a \in PublicKey : IsAccountOpen(ledger, a)} IN
        LET topBlocks == {TopBlock(ledger, a) : a \in openAccounts} IN
        LET accountBalances ==
            LET f(hash) == BalanceAt(ledger, hash) IN BagOfAll(f, SetToBag(topBlocks))
        IN
        /\ GenesisBlockExists => SumBag(accountBalances) <= GenesisBalance

SafetyInvariant == CryptographicInvariant

\* Genesis block creation.
CreateGenesisBlock(privateKey) ==
    LET publicKey == KeyPair[privateKey] IN
    LET genesisBlock == [type |-> "genesis", account |-> publicKey,
                         balance |-> GenesisBalance] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(genesisBlock, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |-> [distributedLedger[n] EXCEPT ![lastHash'] =
            [block |-> genesisBlock,
             signature |-> SignHash(lastHash', privateKey)]]]
    /\ UNCHANGED received

\* Open block validation: the source must be a send to the account being opened.
ValidateOpenBlock(ledger, block) ==
    /\ block.type = "open"
    /\ ledger[block.source] # NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = block.account

CreateOpenBlock(node) ==
    LET privateKey == Ownership[node] IN
    LET publicKey == KeyPair[privateKey] IN
    LET ledger == distributedLedger[node] IN
    /\ \E repPublicKey \in PublicKey, srcHash \in Hash :
        LET newOpenBlock == [account |-> publicKey, source |-> srcHash,
                             rep |-> repPublicKey, type |-> "open"] IN
        /\ ValidateOpenBlock(ledger, newOpenBlock)
        /\ CalculateHash(newOpenBlock, lastHash, lastHash')
        /\ received' = [n \in Node |->
            received[n] \cup {[block |-> newOpenBlock,
                signature |-> SignHash(lastHash', privateKey)]}]
    /\ UNCHANGED distributedLedger

ProcessOpenBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node] IN
    LET block == signedBlock.block IN
    /\ ValidateOpenBlock(ledger, block)
    /\ ~IsAccountOpen(ledger, block.account)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(signedBlock.signature, block.account, lastHash')
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
    /\ received' = [received EXCEPT ![node] = @ \ {signedBlock}]

\* Send block validation: the source must exist and the sender must own it.
ValidateSendBlock(ledger, block) ==
    /\ block.type = "send"
    /\ ledger[block.previous] # NoBlock
    /\ block.balance <= BalanceAt(ledger, block.previous)

CreateSendBlock(node) ==
    LET privateKey == Ownership[node] IN
    LET publicKey == KeyPair[privateKey] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prevHash \in Hash :
        /\ ledger[prevHash] # NoBlock
        /\ PublicKeyOf(ledger, prevHash) = publicKey
        /\ \E recipient \in PublicKey, newBalance \in AccountBalance :
            LET newSendBlock == [previous |-> prevHash, balance |-> newBalance,
                                 destination |-> recipient, type |-> "send"] IN
            /\ ValidateSendBlock(ledger, newSendBlock)
            /\ CalculateHash(newSendBlock, lastHash, lastHash')
            /\ received' = [n \in Node |->
                received[n] \cup {[block |-> newSendBlock,
                    signature |-> SignHash(lastHash', privateKey)]}]
    /\ UNCHANGED distributedLedger

ProcessSendBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node] IN
    LET block == signedBlock.block IN
    /\ ValidateSendBlock(ledger, block)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(signedBlock.signature,
        PublicKeyOf(ledger, block.previous), lastHash')
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
    /\ received' = [received EXCEPT ![node] = @ \ {signedBlock}]

\* Receive block validation: the source must be a send to the receiving account.
ValidateReceiveBlock(ledger, block) ==
    /\ block.type = "receive"
    /\ ledger[block.previous] # NoBlock
    /\ ledger[block.source] # NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = PublicKeyOf(ledger, block.previous)

CreateReceiveBlock(node) ==
    LET privateKey == Ownership[node] IN
    LET publicKey == KeyPair[privateKey] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prevHash \in Hash :
        /\ ledger[prevHash] # NoBlock
        /\ PublicKeyOf(ledger, prevHash) = publicKey
        /\ \E srcHash \in Hash :
            LET newRcvBlock == [previous |-> prevHash, source |-> srcHash,
                                type |-> "receive"] IN
            /\ ValidateReceiveBlock(ledger, newRcvBlock)
            /\ CalculateHash(newRcvBlock, lastHash, lastHash')
            /\ received' = [n \in Node |->
                received[n] \cup {[block |-> newRcvBlock,
                    signature |-> SignHash(lastHash', privateKey)]}]
    /\ UNCHANGED distributedLedger

ProcessReceiveBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node] IN
    LET block == signedBlock.block IN
    /\ ValidateReceiveBlock(ledger, block)
    /\ ~IsSendReceived(ledger, block.source)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(signedBlock.signature,
        PublicKeyOf(ledger, block.previous), lastHash')
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
    /\ received' = [received EXCEPT ![node] = @ \ {signedBlock}]

\* Change block validation: the source must exist and the signer must own it.
ValidateChangeBlock(ledger, block) ==
    /\ block.type = "change"
    /\ ledger[block.previous] # NoBlock

CreateChangeRepBlock(node) ==
    LET privateKey == Ownership[node] IN
    LET publicKey == KeyPair[privateKey] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prevHash \in Hash :
        /\ ledger[prevHash] # NoBlock
        /\ PublicKeyOf(ledger, prevHash) = publicKey
        /\ \E newRep \in PublicKey :
            LET newChangeRepBlock == [previous |-> prevHash, rep |-> newRep,
                                      type |-> "change"] IN
            /\ ValidateChangeBlock(ledger, newChangeRepBlock)
            /\ CalculateHash(newChangeRepBlock, lastHash, lastHash')
            /\ received' = [n \in Node |->
                received[n] \cup {[block |-> newChangeRepBlock,
                    signature |-> SignHash(lastHash', privateKey)]}]
    /\ UNCHANGED distributedLedger

ProcessChangeRepBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node] IN
    LET block == signedBlock.block IN
    /\ ValidateChangeBlock(ledger, block)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(signedBlock.signature,
        PublicKeyOf(ledger, block.previous), lastHash')
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
    /\ received' = [received EXCEPT ![node] = @ \ {signedBlock}]

CreateBlock(node) ==
    \/ CreateOpenBlock(node) \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node) \/ CreateChangeRepBlock(node)

ProcessBlock(node) ==
    /\ \E block \in received[node] :
        \/ ProcessOpenBlock(node, block) \/ ProcessSendBlock(node, block)
        \/ ProcessReceiveBlock(node, block) \/ ProcessChangeRepBlock(node, block)
    /\ received' = [received EXCEPT ![node] = @ \ {block}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E account \in PrivateKey : CreateGenesisBlock(account)
    \/ \E node \in Node : CreateBlock(node) \/ ProcessBlock(node)

Spec == /\ Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

====