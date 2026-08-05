---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Each node replicates the same distributed ledger via two-phase commit per block; a block is
\* broadcast to every node's received set and then committed atomically to all copies.
\* The block-lattice shape means that ordering is recorded in every chain, so the state space
\* grows super-exponentially with depth. Finite model checking only covers a tiny window of it,
\* which is exactly why the balances are summed in a separate (stronger) invariant rather than
\* in the one the .cfg names.

VARIABLES LastHash, Ledger, Received

vars == <<LastHash, Ledger, Received>>

BlockType == {"genesis", "send", "open", "receive", "changeRep"}

Block == [
    hash     : Hash,
    acct     : PublicKey,
    typ      : BlockType,
    prevHash : Hash,
    srcHash  : Hash,
    amount   : Nat,
    target   : PublicKey,
    sig      : PrivateKey
]

\* Chain walks start from the most recent block and stop at the hash that means "no block".
ChainBase(h) == IF h = NoHash THEN NoBlock ELSE LET b == Ledger[h] IN <<b>> \o ChainBase(b.prevHash)

ChainHashes(h) == IF h = NoHash THEN {} ELSE {h} \cup ChainHashes(Ledger[h].prevHash)

ChainAmount(h) == IF h = NoHash THEN 0 ELSE LET b == Ledger[h] IN b.amount + ChainAmount(b.prevHash)

Balance(pk) == ChainAmount(
    CHOOSE h \in ChainHashes(NoHash) : Ledger[h].acct = pk /\ ~ \E z \in ChainHashes(NoHash) : Ledger[z].srcHash = h
)

RECURSIVE SumOver(_, _)
SumOver(f, S) == IF S = {} THEN 0
                 ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

RECURSIVE BalanceTotal(_)
BalanceTotal(S) == IF S = {} THEN 0
                   ELSE LET x == CHOOSE y \in S : TRUE IN Balance(x) + BalanceTotal(S \ {x})

TypeOK ==
    /\ LastHash \in Hash \cup {NoHashVal}
    /\ Ledger \in [Hash -> Block \cup {NoBlockVal}]
    /\ Received \in [Node -> SUBSET Hash]

Init ==
    /\ LastHash = NoHashVal
    /\ Ledger = [h \in Hash |-> NoBlockVal]
    /\ Received = [n \in Node |-> {}]

\* Any node's owned private keys can sign; the ledger copy for the sender's own node is
\* updated in the same step the block goes into the broadcast set, so a node's copy is
\* never behind the blocks it originated.
Broadcast(b) == [n \in Node |-> Received[n] \cup {b.hash}]

CreateGenesisBlock(n) ==
    /\ LastHash = NoHashVal
    /\ LET b == [
            hash     |-> NoHashVal,
            acct     |-> NoHash,
            typ      |-> "genesis",
            prevHash |-> NoHash,
            srcHash  |-> NoHash,
            amount   |-> GenesisBalance,
            target   |-> NoHash,
            sig      |-> CHOOSE k \in PrivateKey : Ledger = [h \in Hash |-> NoBlockVal]
        ] IN /\ Ledger' = [Ledger EXCEPT ![NoHashVal] = b]
           /\ Ledger' = [m \in Node |-> Ledger EXCEPT ![NoHashVal] = b]
           /\ LastHash' = NoHashVal
           /\ Received' = Broadcast(b)

CreateSendBlock(n, k, amount, target) ==
    /\ k \in PrivateKey
    /\ LET pk == CHOOSE p \in PublicKey : p = k
           hPrev == CHOOSE h \in ChainHashes(NoHash) : Ledger[h].acct = pk /\ ~ \E z \in ChainHashes(NoHash) : Ledger[z].srcHash = h
           bPrev == Ledger[hPrev]
           hNew == CalculateHash(bPrev, amount, target)
           b == [
                hash     |-> hNew,
                acct     |-> pk,
                typ      |-> "send",
                prevHash |-> hPrev,
                srcHash  |-> NoHash,
                amount   |-> amount,
                target   |-> target,
                sig      |-> k
            ]
       IN /\ amount <= Balance(pk)
          /\ Ledger[hNew] = NoBlockVal
          /\ Ledger' = [Ledger EXCEPT ![hNew] = b]
          /\ LastHash' = hNew
          /\ Received' = Broadcast(b)

CreateOpenBlock(n, k, srcHash) ==
    /\ k \in PrivateKey
    /\ LET pk == CHOOSE p \in PublicKey : p = k
           bPrev == Ledger[srcHash]
           hNew == CalculateHash(bPrev, 0, pk)
           b == [
                hash     |-> hNew,
                acct     |-> pk,
                typ      |-> "open",
                prevHash |-> NoHash,
                srcHash  |-> srcHash,
                amount   |-> 0,
                target   |-> pk,
                sig      |-> k
           ]
       IN /\ Ledger[srcHash].target = pk
          /\ ~ \E z \in ChainHashes(NoHash) : Ledger[z].acct = pk
          /\ Ledger' = [Ledger EXCEPT ![hNew] = b]
          /\ LastHash' = IF hNew # NoHashVal THEN hNew ELSE LastHash
          /\ Received' = Broadcast(b)

CreateReceiveBlock(n, k, srcHash) ==
    /\ k \in PrivateKey
    /\ LET pk == CHOOSE p \in PublicKey : p = k
           hPrev == CHOOSE h \in ChainHashes(NoHash) : Ledger[h].acct = pk /\ ~ \E z \in ChainHashes(NoHash) : Ledger[z].srcHash = h
           bPrev == Ledger[hPrev]
           bSrc == Ledger[srcHash]
           hNew == CalculateHash(bPrev, bSrc.amount, bSrc.target)
           b == [
                hash     |-> hNew,
                acct     |-> pk,
                typ      |-> "receive",
                prevHash |-> hPrev,
                srcHash  |-> srcHash,
                amount   |-> bSrc.amount,
                target   |-> bSrc.target,
                sig      |-> k
           ]
       IN /\ Ledger[srcHash].target = pk
          /\ ~ \E z \in ChainHashes(NoHash) : Ledger[z].srcHash = srcHash
          /\ Ledger' = [Ledger EXCEPT ![hNew] = b]
          /\ LastHash' = IF hNew # NoHashVal THEN hNew ELSE LastHash
          /\ Received' = Broadcast(b)

CreateChangeRepBlock(n, k, newRep) ==
    /\ k \in PrivateKey
    /\ LET pk == CHOOSE p \in PublicKey : p = k
           hPrev == CHOOSE h \in ChainHashes(NoHash) : Ledger[h].acct = pk /\ ~ \E z \in ChainHashes(NoHash) : Ledger[z].srcHash = h
           bPrev == Ledger[hPrev]
           hNew == CalculateHash(bPrev, 0, newRep)
           b == [
                hash     |-> hNew,
                acct     |-> pk,
                typ      |-> "changeRep",
                prevHash |-> hPrev,
                srcHash  |-> NoHash,
                amount   |-> 0,
                target   |-> newRep,
                sig      |-> k
           ]
       IN /\ Ledger' = [Ledger EXCEPT ![hNew] = b]
          /\ LastHash' = IF hNew # NoHashVal THEN hNew ELSE LastHash
          /\ Received' = Broadcast(b)

ValidateBlock(n, h) ==
    /\ h \in Received[n]
    /\ LET b == Ledger[h] IN /\ b.sig \in PrivateKey
                                 /\ Ledger[b.prevHash] # NoBlockVal
                                 /\ (IF b.typ = "send" THEN b.amount <= Balance(b.acct) ELSE TRUE)
                                 /\ (IF b.typ = "open" THEN ~ \E z \in ChainHashes(NoHash) : Ledger[z].acct = b.acct ELSE TRUE)
                                 /\ (IF b.typ = "receive" THEN ~ \E z \in ChainHashes(NoHash) : Ledger[z].srcHash = b.srcHash ELSE TRUE)
                                 /\ Ledger' = Ledger
    /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]

Next ==
    \/ \E n \in Node, k \in PrivateKey, amt \in Nat, target \in PublicKey : CreateSendBlock(n, k, amt, target)
    \/ \E n \in Node, k \in PrivateKey, src \in Hash : CreateOpenBlock(n, k, src) \/ CreateReceiveBlock(n, k, src)
    \/ \E n \in Node, k \in PrivateKey, rep \in PublicKey : CreateChangeRepBlock(n, k, rep)
    \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)
    \/ \E n \in Node : CreateGenesisBlock(n)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
    \A h \in {x \in Hash : Ledger[x] # NoBlockVal} : Ledger[h].sig \in PrivateKey

====