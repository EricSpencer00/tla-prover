---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash

\* An Ed25519-style signature is a pair of a private key and a hash: Verify(sig,
\* hash) is true only when sig's private key maps to the public key that owns
\* the block being signed. A Blake2b-style hash is modeled abstractly as an
\* external operator, so it is declared here and substituted with a concrete
\* bounded definition in the .cfg (CalculateHashImpl).

VARIABLES lastHash, ledger, receives

vars == <<lastHash, ledger, receives>>

\* A block records the account chain it belongs to, the previous block on that
\* chain, and an optional second predecessor for receive blocks; the type
\* determines which predecessor is used.
BlockType == {"send", "receive", "open", "change"}

Block ==
  [type : BlockType, account : PublicKey, pred1 : Hash, pred2 : Hash,
   amount : Nat, signature : (PrivateKey \X Hash)]

\* ownerOf returns the account that owns a hash, derived from its block record.
ownerOf(h) == LET b == CHOOSE e \in ledger : e[h] # NoBlockVal IN b[h].account

\* balanceOf recursively walks an account chain, summing received minus sent.
Sum(f) == LET g[S \in SUBSET Nat] ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + g[S \ {x})
  IN g[Domain(f)]
BalanceOfChain(h, chain) ==
  LET signs == {k \in chain : chain[k].type = "send"}
      recvs == {k \in chain : chain[k].type = "receive"}
  IN Sum([k \in signs |-> chain[k].amount]) - Sum([k \in recvs |-> chain[k].amount])

BalanceOf(account) == BalanceOfChain(ownerOf(h), ledger[ownerOf(h)])

\* The chain must be contiguous: every block's predecessor must be present and
\* belong to the same account, so the recursive balance is well-founded.
Contiguous(chain) ==
  LET hasPrev(k) ==
    IF k = NoHash THEN TRUE
    ELSE chain[k].type \in {"send", "change", "open"} => chain[k].pred1 # NoHash /\ chain[k].pred1 \in Domain(chain)
    /\ chain[k].type = "receive" => chain[k].pred2 # NoHash /\ chain[k].pred2 \in Domain(chain)
    /\ (chain[k].type # "open" => ownerOf(chain[k].pred1) = chain[k].account)
    /\ (chain[k].type = "receive" => ownerOf(chain[k].pred2) = chain[k].account)
    /\ hasPrev(chain[k].pred1)
    /\ (chain[k].type # "receive" => TRUE)
    /\ (chain[k].type = "receive" => hasPrev(chain[k].pred2))
  IN hasPrev(NoHash)

\* A block's signature must pair the private key that maps to the account's
\* public key with the hash of the block being signed.
SignatureValid(b) == LET p == CHOOSE k \in PrivateKey : ownerOf(b.pred1) = (IF b.type = "open" THEN PublicKey ELSE PublicKey)
  IN b.signature = <<p, b.pred1>> /\ (p \in Node => ownerOf(b.account) = PublicKey)

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ receives \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ receives = [n \in Node |-> {}]

\* A different CalculateHashImpl is substituted in the .cfg for model checking.
HashFunction(h) == IF lastHash = NoHashVal THEN CalculateHash(h) ELSE CalculateHash(lastHash, h)

CreateGenesis(n, h) ==
  /\ lastHash = NoHashVal
  /\ \A m \in Node : ledger[m][h] = NoBlockVal
  /\ HashFunction(h) = h
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [type |-> "open", account |-> ownerOf(h), pred1 |-> NoHash, pred2 |-> NoHash, amount |-> GenesisBalance, signature |-> <<n, NoHash>>]]]
  /\ lastHash' = h
  /\ UNCHANGED receives

CreateSend(n, h, amount) ==
  /\ lastHash # NoHashVal
  /\ \A m \in Node : ledger[m][h] = NoBlockVal
  /\ HashFunction(h) = h
  /\ BalanceOf(ownerOf(h)) >= amount
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [type |-> "send", account |-> ownerOf(h), pred1 |-> lastHash, pred2 |-> NoHash, amount |-> amount, signature |-> <<n, lastHash>>]]]
  /\ lastHash' = h
  /\ receives' = [m \in Node |-> receives[m] \cup {h}]

CreateOpen(n, h, source) ==
  /\ lastHash # NoHashVal
  /\ \A m \in Node : ledger[m][h] = NoBlockVal
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [type |-> "open", account |-> ownerOf(h), pred1 |-> NoHash, pred2 |-> NoHash, amount |-> 0, signature |-> <<n, NoHash>>]]]
  /\ lastHash' = h
  /\ receives' = [m \in Node |-> receives[m] \cup {h}]

CreateReceive(n, h, source) ==
  /\ lastHash # NoHashVal
  /\ \A m \in Node : ledger[m][h] = NoBlockVal
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [type |-> "receive", account |-> ownerOf(h), pred1 |-> lastHash, pred2 |-> source, amount |-> 0, signature |-> <<n, lastHash>>]]]
  /\ lastHash' = h
  /\ receives' = [m \in Node |-> receives[m] \cup {h}]

CreateChange(n, h) ==
  /\ lastHash # NoHashVal
  /\ \A m \in Node : ledger[m][h] = NoBlockVal
  /\ lastHash' = h
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [type |-> "change", account |-> ownerOf(h), pred1 |-> lastHash, pred2 |-> NoHash, amount |-> 0, signature |-> <<n, lastHash>>]]]
  /\ UNCHANGED receives

\* Each node validates only against its own copy of the ledger, never against
\* the global ledger directly, so the validator set is the same for every node.
Validate(n) ==
  /\ \E h \in receives[n] : ledger[n][h] = NoBlockVal
  /\ \E h \in receives[n] :
       /\ SignatureValid(ledger[n][h])
       /\ (IF ledger[n][h].type = "open" THEN ledger[n][h].amount = 0 ELSE TRUE)
       /\ (IF ledger[n][h].type = "send" THEN BalanceOf(ledger[n][h].account) >= ledger[n][h].amount ELSE TRUE)
       /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = ledger[n][h]]]
       /\ receives' = [receives EXCEPT ![n] = receives[n] \ {h}]
  /\ UNCHANGED lastHash

Next == \E n \in Node :
  \/ \E h \in Hash : CreateGenesis(n, h) \/ CreateOpen(n, h, NoHash) \/ CreateChange(n, h)
  \/ \E h \in Hash, amount \in 1 .. GenesisBalance : CreateSend(n, h, amount)
  \/ \E h \in Hash, source \in Hash : CreateReceive(n, h, source)
  \/ Validate(n)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must have a signature that maps back to
\* that block's owning account, not a stale or forged one.
SafetyInvariant ==
  \A n \in Node :
    \A h \in Hash : ledger[n][h] # NoBlockVal => SignatureValid(ledger[n][h])

====