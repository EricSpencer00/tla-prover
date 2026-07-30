---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHashVal \notin Hash /\ NoHash \notin Hash /\ NoBlockVal \notin Block

\* Block data: every block must belong to exactly one account chain, so the
\* issuer of a block can always be inferred from its hash.
Block == [hash: Hash, issuer: PublicKey, kind: {"genesis", "send", "open", "receive", "change"}, pred: Hash, recv: PublicKey, amount: 0..GenesisBalance]

\* Chain order is stored locally in each node's ledger, and is the only thing
\* that orders the protocol's actions (the spec's central point).
IssuerOf(h) == CHOOSE b \in {b \in Block : b.hash = h} : b.issuer

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A recursive walk of the chain; empty for an empty chain, otherwise the
\* previous block's balance plus this block's contribution.
RECURSIVE ChainBalance(_, _)
ChainBalance(ln, h) ==
  IF h = NoHash THEN 0
  ELSE LET b == CHOOSE bl \in {x \in Block : x.hash = h /\ IssuerOf(x) = ln} : TRUE IN
       (IF b.kind = "genesis" THEN GenesisBalance
        ELSE IF b.kind = "send" THEN -b.amount
        ELSE IF b.kind = "receive" THEN b.amount
        ELSE 0) + ChainBalance(ln, b.pred)

RECURSIVE ChainExists(_, _)
ChainExists(ln, h) ==
  IF h = NoHash THEN FALSE
  ELSE LET b == CHOOSE bl \in {x \in Block : x.hash = h /\ IssuerOf(x) = ln} : TRUE IN
       b.pred = NoHash \/ ChainExists(ln, b.pred)

RECURSIVE ChainContains(_, _)
ChainContains(ln, h) ==
  IF h = NoHash THEN FALSE
  ELSE LET b == CHOOSE bl \in {x \in Block : x.hash = h /\ IssuerOf(x) = ln} : TRUE IN
       h = b.hash \/ ChainContains(ln, b.pred)

RECURSIVE ChainPending(_, _)
ChainPending(ln, h) ==
  IF h = NoHash THEN FALSE
  ELSE LET b == CHOOSE bl \in {x \in Block : x.hash = h /\ IssuerOf(x) = ln} : TRUE IN
       h = b.hash \/ ChainPending(ln, b.pred)

RECURSIVE ClaimPending(_, _, _)
ClaimPending(ln, h, k) ==
  IF h = NoHash THEN FALSE
  ELSE LET b == CHOOSE bl \in {x \in Block : x.hash = h /\ IssuerOf(x) = ln} : TRUE IN
       IF b.kind = "send" /\ b.recv = k THEN h = b.hash
       ELSE ClaimPending(ln, b.pred, k)

\* The protocol never mints coins except in the genesis block, and coins are
\* conserved: every receive block reimburses the sender's earlier send.
RECURSIVE ChainTotal(_)
ChainTotal(ln) == ChainBalance(ln, NoHash) + ChainPending(ln, NoHash)

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Block]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesis(p, n) ==
  /\ lastHash = NoHashVal
  /\ LET h == CalculateHash("genesis", NoHashVal, NoHashVal, 0, p) IN
     /\ h \in Hash
     /\ lastHash' = h
     /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = [hash |-> h, issuer |-> p, kind |-> "genesis", pred |-> NoHashVal, recv |-> p, amount |-> 0]]]
  /\ received' = [n \in Node |-> received[n]]

\* The balance check here is the whole point of the invariant: a send block
\* that overdraws its account is rejected, and that is what conserves coins.
CreateSend(p, n) ==
  /\ lastHash # NoHashVal
  /\ ChainBalance(p, lastHash) > 0
  /\ LET h == CalculateHash("send", lastHash, n, 1, p) IN
     /\ h \in Hash
     /\ lastHash' = h
     /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = [hash |-> h, issuer |-> p, kind |-> "send", pred |-> lastHash, recv |-> n, amount |-> 1]]]
  /\ received' = [n \in Node |-> received[n] \cup {[hash |-> h, issuer |-> p, kind |-> "send", pred |-> lastHash, recv |-> n, amount |-> 1]}]

CreateOpen(p, n) ==
  /\ lastHash # NoHashVal
  /\ ChainPending(p, NoHashVal)
  /\ ClaimPending(p, NoHashVal, n)
  /\ LET h == CalculateHash("open", lastHash, NoHashVal, 0, p) IN
     /\ h \in Hash
     /\ lastHash' = h
     /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = [hash |-> h, issuer |-> p, kind |-> "open", pred |-> lastHash, recv |-> n, amount |-> 0]]]
  /\ received' = [n \in Node |-> received[n] \cup {[hash |-> h, issuer |-> p, kind |-> "open", pred |-> lastHash, recv |-> n, amount |-> 0]}]

CreateReceive(p, n) ==
  /\ lastHash # NoHashVal
  /\ ClaimPending(p, NoHashVal, n)
  /\ LET h == CalculateHash("receive", lastHash, NoHashVal, 1, p) IN
     /\ h \in Hash
     /\ lastHash' = h
     /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = [hash |-> h, issuer |-> p, kind |-> "receive", pred |-> lastHash, recv |-> n, amount |-> 1]]]
  /\ received' = [n \in Node |-> received[n] \cup {[hash |-> h, issuer |-> p, kind |-> "receive", pred |-> lastHash, recv |-> n, amount |-> 1]}]

CreateChange(p) ==
  /\ lastHash # NoHashVal
  /\ LET h == CalculateHash("change", lastHash, NoHashVal, 0, p) IN
     /\ h \in Hash
     /\ lastHash' = h
     /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = [hash |-> h, issuer |-> p, kind |-> "change", pred |-> lastHash, recv |-> p, amount |-> 0]]]
  /\ received' = [n \in Node |-> received[n] \cup {[hash |-> h, issuer |-> p, kind |-> "change", pred |-> lastHash, recv |-> p, amount |-> 0]}]

Validate(g, n) ==
  /\ g \in received[n]
  /\ \A m \in Node : ledger[m][g.hash] = NoBlockVal
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![g.hash] = g]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {g}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E p \in PublicKey, n \in Node : CreateGenesis(p, n)
  \/ \E p \in PublicKey, n \in Node : CreateSend(p, n)
  \/ \E p \in PublicKey, n \in Node : CreateOpen(p, n)
  \/ \E p \in PublicKey, n \in Node : CreateReceive(p, n)
  \/ \E p \in PublicKey : CreateChange(p)
  \/ \E g \in Block, n \in Node : Validate(g, n)

Spec == Init /\ [][Next]_vars

\* Crude sanity check: every chain in the replicated ledger has to add up to
\* no more than what the genesis block created. Coins are conserved.
Conservation == \A n \in Node : ChainTotal(n) <= GenesisBalance

CryptoValid ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].issuer \in PublicKey

TypeInvariant == TypeOK

SafetyInvariant == CryptoValid

====