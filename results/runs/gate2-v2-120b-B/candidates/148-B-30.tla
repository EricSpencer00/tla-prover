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

\* ----------------------------------------------------------------------
\* Cryptographic primitives (kept simple for model checking)
\* ----------------------------------------------------------------------
SignHash(hash, privateKey) ==
    [data       |-> hash,
     signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature ==
    [data       : Hash,
     signedWith : PrivateKey]

\* ----------------------------------------------------------------------
\* Block definitions
\* ----------------------------------------------------------------------
AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type    |-> "genesis",
     account |-> CHOOSE pk \in PublicKey : TRUE,
     balance |-> GenesisBalance]

SendBlock ==
    [previous    |-> CHOOSE h \in Hash : TRUE,
     balance     |-> CHOOSE b \in AccountBalance : TRUE,
     destination |-> CHOOSE pk \in PublicKey : TRUE,
     type        |-> "send"]

OpenBlock ==
    [account |-> CHOOSE pk \in PublicKey : TRUE,
     source  |-> CHOOSE h \in Hash : TRUE,
     rep     |-> CHOOSE pk \in PublicKey : TRUE,
     type    |-> "open"]

ReceiveBlock ==
    [previous |-> CHOOSE h \in Hash : TRUE,
     source   |-> CHOOSE h \in Hash : TRUE,
     type     |-> "receive"]

ChangeRepBlock ==
    [previous |-> CHOOSE h \in Hash : TRUE,
     rep      |-> CHOOSE pk \in PublicKey : TRUE,
     type     |-> "change"]

Block ==
    GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

SignedBlock ==
    [block     : Block,
     signature : Signature]

NoBlock == CHOOSE b : b \notin SignedBlock
NoHash  == CHOOSE h : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
GenesisBlockExists ==
    lastHash /= NoHash

IsAccountOpen(ledger, publicKey) ==
    \E hash \in Hash :
        LET sb == ledger[hash] IN
        sb /= NoBlock /\ sb.block.type \in {"genesis", "open"} /\ sb.block.account = publicKey

IsSendReceived(ledger, sourceHash) ==
    \E hash \in Hash :
        LET sb == ledger[hash] IN
        sb /= NoBlock /\ sb.block.type \in {"open", "receive"} /\ sb.block.source = sourceHash

\* ----------------------------------------------------------------------
\* Recursive functions
\* ----------------------------------------------------------------------
RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, blockHash) ==
    LET sb == ledger[blockHash] IN
    IF sb = NoBlock THEN CHOOSE pk \in PublicKey : TRUE
    ELSE
        LET b == sb.block IN
        IF b.type \in {"genesis", "open"} THEN b.account
        ELSE PublicKeyOf(ledger, b.previous)

RECURSIVE BalanceAt(_, _)
BalanceAt(ledger, hash) ==
    LET sb == ledger[hash] IN
    IF sb = NoBlock THEN 0
    ELSE
        LET b == sb.block IN
        CASE b.type = "open"    -> ValueOfSendBlock(ledger, b.source)
           [] b.type = "send"   -> b.balance
           [] b.type = "receive" ->
                BalanceAt(ledger, b.previous) + ValueOfSendBlock(ledger, b.source)
           [] b.type = "change" -> BalanceAt(ledger, b.previous)
           [] b.type = "genesis"-> b.balance

RECURSIVE ValueOfSendBlock(_, _)
ValueOfSendBlock(ledger, hash) ==
    LET sb == ledger[hash] IN
    IF sb = NoBlock THEN 0
    ELSE
        LET b == sb.block IN
        BalanceAt(ledger, b.previous) - b.balance

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        \A hash \in Hash :
            LET sb == ledger[hash] IN
            sb /= NoBlock =>
                LET pk == PublicKeyOf(ledger, hash) IN
                ValidateSignature(sb.signature, pk, hash)

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE
        LET e == CHOOSE x \in S : TRUE IN
        e + SumBag(B \ {e})

BalanceInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        LET openAccs == {pk \in PublicKey : IsAccountOpen(ledger, pk)} IN
        LET topHashes == {TopBlock(ledger, pk) : pk \in openAccs} IN
        LET balBag == BagOfAll( \hash -> BalanceAt(ledger, \hash), SetToBag(topHashes)) IN
        (\A pk \in PublicKey : IsAccountOpen(ledger, pk)) =>
            SumBag(balBag) <= GenesisBalance

SafetyInvariant == CryptographicInvariant

\* ----------------------------------------------------------------------
\* Genesis creation (unchanged semantics)
\* ----------------------------------------------------------------------
CreateGenesisBlock(privateKey) ==
    LET pub == KeyPair[privateKey] IN
    LET gblk ==
        [type    |-> "genesis",
         account |-> pub,
         balance |-> GenesisBalance] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(gblk, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |-> [h \in Hash |-> NoBlock] EXCEPT ![lastHash'] = 
            [block     |-> gblk,
             signature |-> SignHash(lastHash', privateKey)]]
    /\ UNCHANGED received

\* ----------------------------------------------------------------------
\* Validation predicates (fixed field access)
\* ----------------------------------------------------------------------
ValidateOpenBlock(ledger, block) ==
    /\ block.type = "open"
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = block.account

ValidateSendBlock(ledger, block) ==
    /\ block.type = "send"
    /\ ledger[block.previous] /= NoBlock
    /\ block.balance <= BalanceAt(ledger, block.previous)

ValidateReceiveBlock(ledger, block) ==
    /\ block.type = "receive"
    /\ ledger[block.previous] /= NoBlock
    /\ ledger[block.source]   /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = PublicKeyOf(ledger, block.previous)

ValidateChangeBlock(ledger, block) ==
    /\ block.type = "change"
    /\ ledger[block.previous] /= NoBlock

\* ----------------------------------------------------------------------
\* Creation actions (unchanged except for using the corrected validators)
\* ----------------------------------------------------------------------
CreateOpenBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    \E rep \in PublicKey :
        \E src \in Hash :
            LET new ==
                [type    |-> "open",
                 account |-> pub,
                 source  |-> src,
                 rep     |-> rep] IN
            /\ ValidateOpenBlock(ledger, new)
            /\ CalculateHash(new, lastHash, lastHash')
            /\ received' = [received EXCEPT ![node] = @ \cup
                 {[block |-> new,
                   signature |-> SignHash(lastHash', priv)}]]
            /\ UNCHANGED distributedLedger

CreateSendBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    \E prev \in Hash :
        ledger[prev] /= NoBlock /\ PublicKeyOf(ledger, prev) = pub
        /\ \E dst \in PublicKey :
            \E bal \in AccountBalance :
                LET new ==
                    [type        |-> "send",
                     previous    |-> prev,
                     balance     |-> bal,
                     destination |-> dst] IN
                /\ ValidateSendBlock(ledger, new)
                /\ CalculateHash(new, lastHash, lastHash')
                /\ received' = [received EXCEPT ![node] = @ \cup
                     {[block |-> new,
                       signature |-> SignHash(lastHash', priv)}]]
                /\ UNCHANGED distributedLedger

CreateReceiveBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    \E prev \in Hash :
        ledger[prev] /= NoBlock /\ PublicKeyOf(ledger, prev) = pub
        /\ \E src \in Hash :
            LET new ==
                [type     |-> "receive",
                 previous |-> prev,
                 source   |-> src] IN
            /\ ValidateReceiveBlock(ledger, new)
            /\ CalculateHash(new, lastHash, lastHash')
            /\ received' = [received EXCEPT ![node] = @ \cup
                 {[block |-> new,
                   signature |-> SignHash(lastHash', priv)}]]
            /\ UNCHANGED distributedLedger

CreateChangeRepBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    \E prev \in Hash :
        ledger[prev] /= NoBlock /\ PublicKeyOf(ledger, prev) = pub
        /\ \E newRep \in PublicKey :
            LET new ==
                [type     |-> "change",
                 previous |-> prev,
                 rep      |-> newRep] IN
            /\ ValidateChangeBlock(ledger, new)
            /\ CalculateHash(new, lastHash, lastHash')
            /\ received' = [received EXCEPT ![node] = @ \cup
                 {[block |-> new,
                   signature |-> SignHash(lastHash', priv)}]]
            /\ UNCHANGED distributedLedger

CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeRepBlock(node)

\* ----------------------------------------------------------------------
\* Processing actions (unchanged except for corrected field usage)
\* ----------------------------------------------------------------------
ProcessOpenBlock(node, sb) ==
    LET blk == sb.block IN
    LET ledger == distributedLedger[node] IN
    /\ ValidateOpenBlock(ledger, blk)
    /\ ~IsAccountOpen(ledger, blk.account)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature, blk.account, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ UNCHANGED received

ProcessSendBlock(node, sb) ==
    LET blk == sb.block IN
    LET ledger == distributedLedger[node] IN
    /\ ValidateSendBlock(ledger, blk)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature,
          PublicKeyOf(ledger, blk.previous), lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ UNCHANGED received

ProcessReceiveBlock(node, sb) ==
    LET blk == sb.block IN
    LET ledger == distributedLedger[node] IN
    /\ ValidateReceiveBlock(ledger, blk)
    /\ ~IsSendReceived(ledger, blk.source)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature,
          PublicKeyOf(ledger, blk.previous), lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ UNCHANGED received

ProcessChangeRepBlock(node, sb) ==
    LET blk == sb.block IN
    LET ledger == distributedLedger[node] IN
    /\ ValidateChangeBlock(ledger, blk)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature,
          PublicKeyOf(ledger, blk.previous), lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ UNCHANGED received

ProcessBlock(node) ==
    \E sb \in received[node] :
        (ProcessOpenBlock(node, sb) \/
         ProcessSendBlock(node, sb) \/
         ProcessReceiveBlock(node, sb) \/
         ProcessChangeRepBlock(node, sb))
        /\ received' = [received EXCEPT ![node] = @ \ {sb}]

\* ----------------------------------------------------------------------
\* Init and Next
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E pk \in PrivateKey : CreateGenesisBlock(pk)
    \/ \E n \in Node : CreateBlock(n)
    \/ \E n \in Node : ProcessBlock(n)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

====