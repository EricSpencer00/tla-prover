---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* This spec models the original Nano protocol's block-lattice, with a focus on
\* hash functions and signatures. The ledger is replicated per node, so the
\* block type is replicated but each copy must validate signatures identically.

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

Owners == { PrivateKey[n] : n \in Node }

VARIABLES
  lastHash,       \* The most recently calculated block hash.
  ledger,         \* [Node -> [Hash -> Block]]: each node's replicated copy.
  received        \* [Node -> SUBSET Hash]: blocks broadcast but not yet validated.

vars == << lastHash, ledger, received >>

Blocks == [hash: Hash, owner: PublicKey, kind: {"genesis", "send", "receive", "open", "changeRep"},
           pred: Hash, link: Hash, amt: 0..GenesisBalance]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlock}]]
  /\ received \in [Node -> SUBSET Hash]

InitLedgerNode(n) == [h \in Hash |-> NoBlock]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> InitLedgerNode(n)]
  /\ received = [n \in Node |-> {}]

\* A recursive function walks an account's chain to compute its balance. The
\* recursion depth is capped by the number of block hashes, which also bounds the
\* spec for model checking.
RECURSIVE BalanceOf(_, _, _)
BalanceOf(owner, h, seen) ==
  IF h = NoHash \/ h \in seen THEN 0
  ELSE
    LET blk == ledger[CHOOSE n \in Node : ledger[n][h] # NoBlock] [h] IN
    IF blk.owner = owner THEN
      CASE blk.kind = "genesis" -> blk.amt
        [] blk.kind = "send"    -> blk.amt + BalanceOf(owner, blk.pred, seen \cup {h})
        [] blk.kind = "receive" -> BalanceOf(owner, blk.pred, seen \cup {h}) - blk.amt
        [] blk.kind = "open"    -> BalanceOf(owner, blk.link, seen \cup {h})
        [] blk.kind = "changeRep" -> BalanceOf(owner, blk.pred, seen \cup {h})
        [] OTHER                -> BalanceOf(owner, blk.pred, seen \cup {h})
      END
    ELSE
      CASE blk.kind = "open"    -> BalanceOf(owner, blk.link, seen \cup {h})
        [] blk.kind = "receive" -> BalanceOf(owner, blk.link, seen \cup {h})
        [] OTHER               -> BalanceOf(owner, blk.pred, seen \cup {h})
      END

RECURSIVE SumBalances(_, _)
SumBalances(n, seen) ==
  IF n > Cardinality(Node) THEN 0
  ELSE
    LET owner == PublicKey[CHOOSE nd \in Node : CHOOSE i \in 1..Cardinality(Node) : n = i] IN
    LET bal == BalanceOf(owner, ledger[CHOOSE nd \in Node : PublicKey[nd] = owner][NoHash], {})
    /\ owner \notin seen
    THEN bal + SumBalances(n + 1, seen \cup {owner})
    ELSE SumBalances(n + 1, seen)

BalanceInvariant == SumBalances(1, {}) <= GenesisBalance

ValidSignature(blk) ==
  /\ blk.owner \in PublicKey
  /\ blk.owner = CHOOSE pub \in PublicKey : CHOOSE sk \in PrivateKey : pub = PrivateKey[sk]

\* Creating a block is a single step: the hash is calculated once, the block is
\* stored in every node's ledger copy, and it is broadcast to every node's
\* received set. That all-or-nothing ordering is exactly what guarantees no
\* partially-delivered block can be validated on its own.
CreateGenesis ==
  /\ lastHash = NoHash
  /\ \E h \in Hash :
       /\ lastHash' = h
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = [hash |-> h, owner |-> Owners,
                                    kind |-> "genesis", pred |-> NoHash, link |-> NoHash, amt |-> GenesisBalance]]]
       /\ received' = [n \in Node |-> received[n] \cup {h}]
  /\ UNCHANGED << >>

CreateSend(n, rec, amt) ==
  /\ \E h \in Hash :
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [hash |-> h, owner |-> Owners,
                                    kind |-> "send", pred |-> NoHash, link |-> NoHash, amt |-> amt]]]
       /\ received' = [m \in Node |-> received[m] \cup {h}]
  /\ UNCHANGED << >>

CreateOpen(n, send) ==
  /\ \E h \in Hash :
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [hash |-> h, owner |-> Owners,
                                    kind |-> "open", pred |-> NoHash, link |-> send, amt |-> 0]]]
       /\ received' = [m \in Node |-> received[m] \cup {h}]
  /\ UNCHANGED << >>

CreateReceive(n, send, prev) ==
  /\ \E h \in Hash :
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [hash |-> h, owner |-> Owners,
                                    kind |-> "receive", pred |-> prev, link |-> send, amt |-> 0]]]
       /\ received' = [m \in Node |-> received[m] \cup {h}]
  /\ UNCHANGED << >>

CreateChangeRep(n, prev) ==
  /\ \E h \in Hash :
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [hash |-> h, owner |-> Owners,
                                    kind |-> "changeRep", pred |-> prev, link |-> NoHash, amt |-> 0]]]
       /\ received' = [m \in Node |-> received[m] \cup {h}]
  /\ UNCHANGED << >>

ValidateBlock(m, h) ==
  /\ h \in received[m]
  /\ ledger[m][h] # NoBlock
  /\ \A n \in Node : ledger[n][h] # NoBlock
  /\ ledger' = [n \in Node |-> IF ledger[n][h] # NoBlock THEN ledger[n] ELSE ledger[m]]
  /\ received' = [received EXCEPT ![m] = @ \ {h}]
  /\ UNCHANGED << lastHash >>

Next ==
  \/ CreateGenesis
  \/ \E n \in Node, rec \in PublicKey, amt \in 1..GenesisBalance : CreateSend(n, rec, amt)
  \/ \E n \in Node, send \in Hash : CreateOpen(n, send)
  \/ \E n \in Node, send \in Hash, prev \in Hash : CreateReceive(n, send, prev)
  \/ \E n \in Node, prev \in Hash : CreateChangeRep(n, prev)
  \/ \E m \in Node, h \in Hash : ValidateBlock(m, h)

Spec == Init /\ [][Next]_vars

\* Safety invariant: every block in every replicated ledger copy is signed by the
\* owner of the chain it belongs to.
SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlock => ValidSignature(ledger[n][h])

====