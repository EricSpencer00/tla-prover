---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* NoHash/NoBlock are the "empty" values for the ledger and for block fields;
\* NoHashVal is used for the "no previous hash" sentinel value.
ASSUME NoHash \notin Hash
ASSUME NoBlock \notin Hash
ASSUME NoHashVal \notin Hash

Block == [prev : Hash \cup {NoHash}, senderPub : PublicKey, receiver : PublicKey \cup {"self"}, amt : 0..GenesisBalance, sig : PrivateKey, typ : {"send", "open", "receive", "change", "genesis"}]

\* The chain of a given account is the ordered block sequence reachable by
\* reverse-walking prev-hash links from a block down to genesis.
ChainFor(pub, b) == IF b = NoBlock THEN <<>> ELSE IF b \notin Hash THEN <<>> ELSE
  IF b = NoHash THEN <<>> ELSE
  IF b \in Hash /\ (b \in DOMAIN Ledger) /\ Ledger[b] # NoBlockVal /\ Ledger[b].senderPub = pub
    THEN LET prevChain == ChainFor(pub, Ledger[b].prev) IN <<b>> \o prevChain
    ELSE ChainFor(pub, NoHash)

RECURSIVE BalanceOf(_, _)
BalanceOf(pub, s) == IF s = <<>> THEN 0
  ELSE IF Head(s) = NoBlock THEN BalanceOf(pub, Tail(s))
  ELSE LET h == Head(s) IN
        IF Ledger[h].typ = "send" THEN BalanceOf(pub, Tail(s)) - Ledger[h].amt
        ELSE IF Ledger[h].typ \in {"open", "receive"} THEN BalanceOf(pub, Tail(s)) + Ledger[h].amt
        ELSE BalanceOf(pub, Tail(s))

RECURSIVE TotalBalance(_)
TotalBalance(S) == IF S = {} THEN 0
  ELSE LET pub == CHOOSE e \in S : TRUE IN BalanceOf(pub, ChainFor(pub, NoHash)) + TotalBalance(S \ {pub})

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Hash -> Block \cup {NoBlockVal}]
  /\ received \in [Node -> SUBSET [hash : Hash, node : Node]]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

ValidSignature(b) == \E priv \in PrivateKey : (b.sig = priv) /\ (priv :> PublicKey)[b.senderPub]

\* A block is valid only if every prior block in its own account chain already
\* exists in the *checking* node's local ledger copy.
ChainExists(n, pub, h) == \A i \in 1..Len(ChainFor(pub, h)) : ChainFor(pub, h)[i] \in DOMAIN (ledger[n])

ValidateRecv(n, r) ==
  /\ r.hash \in DOMAIN ledger
  /\ ledger[r.hash] # NoBlockVal
  /\ ChainExists(n, ledger[r.hash].senderPub, r.hash)
  /\ ValidSignature(ledger[r.hash])
  /\ ledger' = [ledger EXCEPT ![r.hash] = ledger[r.hash]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {r}]
  /\ UNCHANGED lastHash

ValidateAll(n) == \E r \in received[n] : ValidateRecv(n, r

CreateGenesisBlock(priv, n) ==
  /\ lastHash = NoHash
  /\ lastHash' = CalculateHash([prev |-> NoHash, senderPub |-> (priv :> PublicKey), receiver |-> "self", amt |-> GenesisBalance, sig |-> priv, typ |-> "genesis"], NoHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [prev |-> NoHash, senderPub |-> (priv :> PublicKey), receiver |-> "self", amt |-> GenesisBalance, sig |-> priv, typ |-> "genesis"]]
  /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', node |-> n]}]

CreateSendBlock(priv, recPub, amt, n) ==
  /\ lastHash # NoHash
  /\ BalanceOf((priv :> PublicKey), ChainFor((priv :> PublicKey), NoHash)) >= amt
  /\ lastHash' = CalculateHash([prev |-> lastHash, senderPub |-> (priv :> PublicKey), receiver |-> recPub, amt |-> amt, sig |-> priv, typ |-> "send"], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [prev |-> lastHash, senderPub |-> (priv :> PublicKey), receiver |-> recPub, amt |-> amt, sig |-> priv, typ |-> "send"]]
  /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', node |-> n]}]

CreateOpenBlock(priv, sendHash, n) ==
  /\ lastHash # NoHash
  /\ sendHash \in DOMAIN ledger
  /\ ledger[sendHash].typ = "send"
  /\ ledger[sendHash].receiver = (priv :> PublicKey)
  /\ \A i \in 1..Len(ChainFor((priv :> PublicKey), NoHash)) : ChainFor((priv :> PublicKey), NoHash)[i] # sendHash
  /\ lastHash' = CalculateHash([prev |-> NoHash, senderPub |-> (priv :> PublicKey), receiver |-> (priv :> PublicKey), amt |-> ledger[sendHash].amt, sig |-> priv, typ |-> "open"], NoHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [prev |-> NoHash, senderPub |-> (priv :> PublicKey), receiver |-> (priv :> PublicKey), amt |-> ledger[sendHash].amt, sig |-> priv, typ |-> "open"]]
  /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', node |-> n]}]

CreateReceiveBlock(priv, sendHash, n) ==
  /\ lastHash # NoHash
  /\ sendHash \in DOMAIN ledger
  /\ ledger[sendHash].typ = "send"
  /\ ledger[sendHash].receiver = (priv :> PublicKey)
  /\ \A i \in 1..Len(ChainFor((priv :> PublicKey), NoHash)) : ChainFor((priv :> PublicKey), NoHash)[i] # sendHash
  /\ lastHash' = CalculateHash([prev |-> lastHash, senderPub |-> (priv :> PublicKey), receiver |-> (priv :> PublicKey), amt |-> ledger[sendHash].amt, sig |-> priv, typ |-> "receive"], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [prev |-> lastHash, senderPub |-> (priv :> PublicKey), receiver |-> (priv :> PublicKey), amt |-> ledger[sendHash].amt, sig |-> priv, typ |-> "receive"]]
  /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', node |-> n]}]

CreateChangeBlock(priv, n) ==
  /\ lastHash # NoHash
  /\ lastHash' = CalculateHash([prev |-> lastHash, senderPub |-> (priv :> PublicKey), receiver |-> "self", amt |-> 0, sig |-> priv, typ |-> "change"], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [prev |-> lastHash, senderPub |-> (priv :> PublicKey), receiver |-> "self", amt |-> 0, sig |-> priv, typ |-> "change"]]
  /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', node |-> n]}]

Next ==
  \/ ValidateAll("n1") \/ ValidateAll("n2")
  \/ \E priv \in PrivateKey, n \in Node : CreateGenesisBlock(priv, n)
  \/ \E priv \in PrivateKey, recPub \in PublicKey, amt \in 1..GenesisBalance, n \in Node : CreateSendBlock(priv, recPub, amt, n)
  \/ \E priv \in PrivateKey, sendHash \in Hash, n \in Node : CreateOpenBlock(priv, sendHash, n)
  \/ \E priv \in PrivateKey, sendHash \in Hash, n \in Node : CreateReceiveBlock(priv, sendHash, n)
  \/ \E priv \in PrivateKey, n \in Node : CreateChangeBlock(priv, n)

Spec == Init /\ [][Next]_vars

\* Every ledger copy across every node must agree on the signature of every
\* block that is recorded anywhere; a forged or stale block would break it.
SafetyInvariant == \A h \in Hash : \A n1, n2 \in Node : (ledger[n1][h] # NoBlockVal /\ ledger[n2][h] # NoBlockVal) => (ledger[n1][h].sig = ledger[n2][h].sig)
====