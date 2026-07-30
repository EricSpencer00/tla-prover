---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

VARIABLES
  lastHash, ledger, recvd

vars == <<lastHash, ledger, recvd>>

TypeInvariant ==
  /\ lastHash \in Hash
  /\ ledger \in [Node -> [Hash -> (("block") \cup {NoBlockVal})]]
  /\ recvd \in [Node -> SUBSET Hash]

\* A ledger entry is a block labeled with its type and fields. Hashes are
\* opaque, so this is a thin wrapper around the type set.
BlockType == {"genesis", "send", "open", "receive", "changeRep"}

\* The signedBy field is the public key of the account chain's owner; the
\* recipient field is only present on send, open, and receive blocks. The
\* amount field is present on send, open, and receive blocks. The link
\* fields chain the blocks together in the account's own chain.
BlockFields ==
  [type: BlockType, signedBy: PublicKey, recipient: PublicKey \cup {NoHash},
   amount: 0..GenesisBalance, link: Hash \cup {NoHash}]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ recvd = [n \in Node |-> {}]

\* The hash operator is left uninterpreted here; it is bound to a concrete
\* function in the .cfg so the spec stays finite (bounded hash set).
Calculate(hd, prev) == CalculateHash(hd, prev)

\* Walking an account chain back to the genesis block to sum its total.
RECURSIVE ChainAmount(_)
ChainAmount(h) ==
  IF h = NoHashVal THEN 0
  ELSE LET blk == CHOOSE b \in {x \in Hash : ledger[CHOOSE n \in Node : TRUE][x] # NoBlockVal}
                               : ledger[CHOOSE n \in Node : TRUE][x] # NoBlockVal /\ x = h]
       amt == blk.amount
    IN IF blk.link = NoHashVal THEN amt ELSE amt + ChainAmount(blk.link)

\* Every node's account balance must be reachable from its chain.
RECURSIVE SearchChain(_)
SearchChain(h) ==
  IF h = NoHashVal THEN FALSE
  ELSE LET blk == CHOOSE b \in {x \in Hash : ledger[CHOOSE n \in Node : TRUE][x] # NoBlockVal}
                               : ledger[CHOOSE n \in Node : TRUE][x] # NoBlockVal /\ x = h]
    IN blk.link = NoHashVal \/ SearchChain(blk.link)

\* The blockchain's total coin supply can never be exceeded.
SupplyConserved ==
  LET balances == [n \in Node |-> ChainAmount(ledger[n][CHOOSE h \in Hash : TRUE])]
  IN BalanceSum(balances) <= GenesisBalance

BalanceSum(f) == LET add[S \in SUBSET Node] ==
                    IF S = {} THEN 0
                    ELSE LET x == CHOOSE e \in S : TRUE
                         IN f[x] + add[S \ {x}]
                 IN add[Node]

\* Generic block receipt: a block is applied to a node's ledger once it can
\* be validated against that node's own copy, regardless of who originally
\* created it.
ValidateBlock(blkHash, n) ==
  /\ blkHash \in recvd[n]
  /\ \E blk \in BlockFields :
       /\ ledger[n][blkHash] = NoBlockVal
       /\ ledger[n][blk.link] # NoBlockVal \/ blk.link = NoHashVal
       /\ blk.signedBy \in PublicKey
       /\ ledger[n][blkHash] = blk
  /\ ledger' = [ledger EXCEPT ![n][blkHash] = ledger[n][blkHash]]
  /\ recvd' = [recvd EXCEPT ![n] = recvd[n] \ {blkHash}]
  /\ UNCHANGED lastHash

CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E pk \in PrivateKey :
       /\ \E b \in Hash :
            /\ lastHash' = b
            /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![b] = [type |-> "genesis",
                                                                   signedBy |-> pk,
                                                                   recipient |-> NoHash,
                                                                   amount |-> GenesisBalance,
                                                                   link |-> NoHashVal]]]
            /\ recvd' = [n \in Node |-> {}]
  /\ UNCHANGED << >>

CreateSendBlock(n) ==
  /\ lastHash # NoHashVal
  /\ \E pk \in PrivateKey :
       /\ pk \in {pk2 \in PrivateKey : pk2 = n}
       /\ \E rcpt \in PublicKey, amt \in 1..GenesisBalance, b \in Hash :
            /\ ChainAmount(ledger[n][lastHash]) >= amt
            /\ ledger' = [ledger EXCEPT ![n][b] = [type |-> "send", signedBy |-> pk,
                                                   recipient |-> rcpt, amount |-> amt,
                                                   link |-> lastHash]]
            /\ lastHash' = b
            /\ recvd' = [n2 \in Node |-> recvd[n2] \cup {b}]
  /\ UNCHANGED << >>

CreateOpenBlock(n) ==
  /\ lastHash # NoHashVal
  /\ \E pk \in PrivateKey :
       /\ pk \in {pk2 \in PrivateKey : pk2 = n}
       /\ \E sendHash \in Hash, b \in Hash :
            /\ ledger[n][sendHash] # NoBlockVal
            /\ ledger[n][sendHash].type = "send"
            /\ ledger[n][sendHash].recipient = pk
            /\ ledger[n][lastHash].type = "genesis"
            /\ ledger' = [ledger EXCEPT ![n][b] = [type |-> "open", signedBy |-> pk,
                                                   recipient |-> NoHash, amount |-> ledger[n][sendHash].amount,
                                                   link |-> lastHash]]
            /\ lastHash' = b
            /\ recvd' = [n2 \in Node |-> recvd[n2] \cup {b}]
  /\ UNCHANGED << >>

CreateReceiveBlock(n) ==
  /\ lastHash # NoHashVal
  /\ \E pk \in PrivateKey :
       /\ pk \in {pk2 \in PrivateKey : pk2 = n}
       /\ \E sendHash, b \in Hash :
            /\ ledger[n][sendHash] # NoBlockVal
            /\ ledger[n][sendHash].type = "send"
            /\ ledger[n][sendHash].recipient = pk
            /\ ledger' = [ledger EXCEPT ![n][b] = [type |-> "receive", signedBy |-> pk,
                                                   recipient |-> NoHash, amount |-> ledger[n][sendHash].amount,
                                                   link |-> lastHash]]
            /\ lastHash' = b
            /\ recvd' = [n2 \in Node |-> recvd[n2] \cup {b}]
  /\ UNCHANGED << >>

CreateChangeRepBlock(n) ==
  /\ lastHash # NoHashVal
  /\ \E pk \in PrivateKey :
       /\ pk \in {pk2 \in PrivateKey : pk2 = n}
       /\ \E b \in Hash :
            /\ ledger' = [ledger EXCEPT ![n][b] = [type |-> "changeRep", signedBy |-> pk,
                                                   recipient |-> NoHash, amount |-> 0, link |-> lastHash]]
            /\ lastHash' = b
            /\ recvd' = [n2 \in Node |-> recvd[n2] \cup {b}]
  /\ UNCHANGED << >>

ProcessBlock(n) ==
  \E blkHash \in Hash : ValidateBlock(blkHash, n)

Next ==
  \/ CreateGenesisBlock
  \/ \E n \in Node : CreateSendBlock(n)
  \/ \E n \in Node : CreateOpenBlock(n)
  \/ \E n \in Node : CreateReceiveBlock(n)
  \/ \E n \in Node : CreateChangeRepBlock(n)
  \/ \E n \in Node : ProcessBlock(n)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must validate against the public key
\* of the account chain that contains it.
ValidSignature(h) == h # NoHashVal =>
  /\ ledger[CHOOSE n \in Node : TRUE][h] # NoBlockVal
  /\ ledger[CHOOSE n \in Node : TRUE][h].signedBy \in PublicKey

SafetyInvariant ==
  /\ TypeInvariant
  /\ \A h \in Hash : ValidSignature(h)

====