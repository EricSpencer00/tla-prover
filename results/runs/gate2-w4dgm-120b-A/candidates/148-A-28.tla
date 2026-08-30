---- MODULE Nano ----
EXTENDS Integers, Sequences

CONSTANTS
  Hash,           \* block hashes (bounded search space for model checking)
  NoHashVal,      \* sentinel hash meaning "no previous block"
  PrivateKey,     \* private keys, each node holds exactly one
  PublicKey,      \* public keys, one per account
  Node,           \* network nodes
  GenesisBalance, \* total coin supply, a natural number
  NoBlockVal,     \* sentinel meaning a block slot is empty
  CalculateHash,  \* abstract hash operator (substituted by CalculateHashImpl)
  NoHash,         \* sentinel hash value
  NoBlock         \* sentinel block value

ASSUME NoHash \notin Hash

\* A signed block's fields, in the order the block chain will walk them
Block == [typ : {"genesis", "send", "open", "receive", "change"},
           prev : Hash,                     \* previous block in this account chain
           link : Hash,                     \* for open/receive: referenced block in the other account
           amt  : Nat,                      \* amount moved (0 for genesis/change)
           sig  : PrivateKey]               \* Ed25519 signature covering the block

\* A signed block stamped with the hash it was recorded under
StampedBlock == [blk : Block, stamp : Hash]

\* The action history is the concatenated log of blocks in one account's chain
Chain == Seq(StampedBlock)

AccountFor(k) == CHOOSE pk \in PublicKey : k = pk

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> StampedBlock \cup {NoBlock}]]
  /\ received \in [Node -> SUBSET StampedBlock]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

\* Balance is the sum of send amounts that have been received by this chain
RECURSIVE SumAmt(_)
SumAmt(s) ==
  IF s = <<>> THEN 0
  ELSE IF Head(s).blk.typ = "receive" THEN Head(s).blk.amt + SumAmt(Tail(s))
  ELSE SumAmt(Tail(s))

Balance(ch) == SumAmt(ch)

\* The chain is walked backwards from its newest block toward the oldest
RECURSIVE WalkChain(_)
WalkChain(ch, h) ==
  IF ch = <<>> THEN {}
  ELSE IF Head(ch).stamp = h THEN {Head(ch)} \cup WalkChain(Tail(ch), h)
  ELSE WalkChain(Tail(ch), h)

ChainForAccount(pk) ==
  CHOOSE ch \in { p \in Chain : p # {} /\ Head(p).blk.sig \in AccountFor(pk) } :
    \A q \in { p \in Chain : p # {} /\ Head(p).blk.sig \in AccountFor(pk) } : Len(p) <= Len(q)

\* Account balance is the balance of its own chain, which may be empty
BalanceOf(pk) == Balance(ChainForAccount(pk))

\* A node's ledger must credit every send it has itself sent
SentOnlyFromOwned(n) ==
  \A h \in Hash :
    ledger[n][h] # NoBlock =>
      ledger[n][h].blk.sig = n

TotalBalance == BalanceOf(AccountFor(Choose n \in Node : TRUE))

\* The chain walks backwards through its own stamps, so blocks are never lost or duplicated
NoLostUpdate ==
  \A n \in Node :
    ChainForAccount(AccountFor(n)) \subseteq WalkChain(ChainForAccount(AccountFor(n)),
                                                      ledger[n][Head(ChainForAccount(AccountFor(n))).stamp].stamp)

\* A signed block is only valid if its Ed25519 signature matches the account that owns it
ValidSignature(b) == b.sig \in AccountFor(Head(ChainForAccount(AccountFor(b.sig))).blk.sig)

\* The chain recording the block is a nonempty suffix of the owner's chain, so no block is lost
RecordedInSuffix(b) ==
  ChainForAccount(AccountFor(b.sig)) # {} /\ ChainForAccount(AccountFor(b.sig)) \subseteq
    WalkChain(ChainForAccount(AccountFor(b.sig)), ledger[AccountFor(b.sig)][Head(ChainForAccount(AccountFor(b.sig)))].stamp)

\* A send block is only valid if the amount stays within the sender's balance
SendWithinBalance(b) ==
  IF b.typ = "send" THEN BalanceOf(AccountFor(b.sig)) >= b.amt ELSE TRUE

\* An open block may only be created against a send directed to this account that is unclaimed
Openable(p) ==
  /\ p.blk.typ = "open"
  /\ ledger[p.blk.sig][p.blk.link] # NoBlock
  /\ \A n \in Node : ledger[n][p.blk.link].blk.typ # "receive"
  /\ ChainForAccount(AccountFor(p.blk.sig)) = {}

\* A receive block may only be created against a send directed to this account that has not been claimed
Receivable(p) ==
  /\ p.blk.typ = "receive"
  /\ ledger[p.blk.sig][p.blk.link] # NoBlock
  /\ \A n \in Node : ledger[n][p.blk.link].blk.typ # "receive"

\* A block is only valid if it passes every check that applies to its type
BlockValid(p) ==
  /\ ValidSignature(p.blk)
  /\ RecordedInSuffix(p.blk)
  /\ SendWithinBalance(p.blk)
  /\ Openable(p)
  /\ Receivable(p)

\* The genesis block creates the whole supply and is recorded everywhere at once
CreateGenesis ==
  /\ lastHash = NoHash
  /\ \E n \in Node :
       \E sk \in PrivateKey :
         LET h == CalculateHash([kind |-> "genesis", amt |-> GenesisBalance, link |-> NoHash, prev |-> NoHash, sig |-> sk])
         IN /\ lastHash' = h
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [blk |-> [typ |-> "genesis", prev |-> NoHash,
                                                                          link |-> NoHash, amt |-> GenesisBalance,
                                                                          sig |-> sk], stamp |-> h]]]
            /\ received' = [m \in Node |-> received[m] \cup {[blk |-> [typ |-> "genesis", prev |-> NoHash,
                                                                    link |-> NoHash, amt |-> GenesisBalance, sig |-> sk],
                                                                  stamp |-> h]}]

\* A block is broadcast to every node's received set
Broadcast(p) ==
  /\ p \in received[AccountFor(p.blk.sig)]
  /\ \A n \in Node : received' = [received EXCEPT ![n] = received[n] \cup {p}]
  /\ UNCHANGED <<lastHash, ledger>>

\* A block is recorded on a node once it passes that node's validation
ProcessBlock(n, p) ==
  /\ p \in received[n]
  /\ BlockValid(p)
  /\ ledger[n][p.stamp] = NoBlock
  /\ ledger' = [ledger EXCEPT ![n][p.stamp] = p]
  /\ received' = [received EXCEPT ![n] = received[n] \ {p}]
  /\ UNCHANGED lastHash

DiscardBlock(n, p) ==
  /\ p \in received[n]
  /\ ~BlockValid(p)
  /\ received' = [received EXCEPT ![n] = received[n] \ {p}]
  /\ UNCHANGED <<lastHash, ledger>>

\* A send, open, receive, or change block is created and broadcast from one node
CreateBlock(n, typ, amt, link) ==
  /\ lastHash # NoHash
  /\ \E sk \in PrivateKey :
       LET h == CalculateHash([kind |-> typ, amt |-> amt, link |-> link,
                               prev |-> Head(ChainForAccount(AccountFor(n))).stamp, sig |-> sk])
           b == [blk |-> [typ |-> typ, prev |-> Head(ChainForAccount(AccountFor(n))).stamp,
                          link |-> link, amt |-> amt, sig |-> sk], stamp |-> h]
       IN /\ (typ = "send" => link \in Hash /\ ledger[n][link].blk.sig \in AccountFor(n))
          /\ (typ \in {"open", "receive"} => link \in Hash)
          /\ ledger' = [m \in Node |-> ledger[m] EXCEPT ![h] = IF m = n THEN b ELSE ledger[m][h]]
          /\ lastHash' = h
          /\ received' = [m \in Node |-> received[m] \cup {b}]

Next ==
  \/ CreateGenesis
  \/ \E n \in Node, p \in StampedBlock : Broadcast(p) \/ ProcessBlock(n, p) \/ DiscardBlock(n, p)
  \/ \E n \in Node, typ \in {"send", "open", "receive", "change"}, amt \in 0..GenesisBalance, link \in Hash \cup {NoHash} :
       CreateBlock(n, typ, amt, link)

Spec == Init /\ [][Next]_vars

\* Type-checking: everything stays inside its declared shape
TypeInvariant == TypeOK

\* Every block in every node's ledger has a valid Ed25519 signature
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlock => ValidSignature(ledger[n][h].blk)

====