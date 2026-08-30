---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* each account's chain is ordered by the hash of the previous block; no hash is ever reused on a chain
\* the hash operator is a constant (not a function) so it can be swapped out per the .cfg
\* balance tracking walks an account chain recursively -- this is where the super-exponential blowup lives

VARIABLES lastHash, ledger, received

vars == << lastHash, ledger, received >>

BlockDom(h) == UNION {ran(ledger[n]) : n \in Node}

AccountChains == UNION { [n \in Node |-> {r.h : r \in {s \in ledger[n] : s.h # NoHash}}] : n \in Node }

SentBlocks(b) == {r \in BlockDom(NoHash) : r.h = b}
ReceivedBy(b) == {n \in Node : b \in {r.h : r \in {s \in ledger[n] : s.h # NoHash}}}

\* the only thing that binds the chain together is the hash of the previous block, so its absence is the entire check
ParentBlockExists(n, b) == \E r \in ledger[n] : r.h # NoHash /\ r.prev = b

RECURSIVE ChainBalance(_)
ChainBalance(n) == IF n = NoHash THEN 0
                   ELSE LET r == CHOOSE e \in ledger[n] : e.h = n /\ r.h # NoHash
                        IN IF r.pt = "genesis" THEN r.amt
                           ELSE IF r.pt = "send" THEN -r.amt
                           ELSE r.amt

RECURSIVE TotalBalance(_)
TotalBalance(S) == IF S = {} THEN 0
                   ELSE LET n == CHOOSE x \in S : TRUE
                        IN ChainBalance(n) + TotalBalance(S \ {n})

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> SUBSET [h: Hash, prev: Hash \cup {NoHash}, pt: {"genesis", "send", "open", "receive", "change"}, amt: 0..GenesisBalance, sender: PublicKey \cup {NoBlock}]]
    /\ received \in [Node -> SUBSET [h: Hash, prev: Hash \cup {NoHash}, pt: {"genesis", "send", "open", "receive", "change"}, amt: 0..GenesisBalance, sender: PublicKey \cup {NoBlock}]]

SafetyInvariant == \A n \in Node, r \in ledger[n] : r.h # NoHash => PublicKey @ PublicKey @@ r.sender

\* the hash ordered chain means reordering is a different history, so the model checks a bounded
\* set of hashes and treats the hash op as a free choice rather than a deterministic function
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> {NoBlockVal}]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n) ==
    /\ lastHash = NoHash
    /\ \A n2 \in Node : NoBlockVal \notin ledger[n2]
    /\ lastHash' = CalculateHash([h |-> NoHash, pt |-> "genesis", amt |-> GenesisBalance, sender |-> NoBlock])
    /\ ledger' = [n2 \in Node |-> IF n2 = n THEN {[h |-> lastHash', prev |-> NoHash, pt |-> "genesis", amt |-> GenesisBalance, sender |-> NoBlock]} ELSE ledger[n2]]
    /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] ELSE received[n2]]

CreateSendBlock(n, b, amt) ==
    /\ b \in BlockDom(NoHash)
    /\ NoHashVal \notin {r.h : r \in ledger[n]}
    /\ ~\E t \in Transaction: t.h = b
    /\ amt <= ChainBalance(n)
    /\ b # NoHash
    /\ lastHash' = CalculateHash([h |-> b, pt |-> "send", amt |-> amt, sender |-> PublicKey @ PrivateKey[n]])
    /\ ledger' = [n2 \in Node |-> IF n2 = n THEN ledger[n] \cup {[h |-> lastHash', prev |-> b, pt |-> "send", amt |-> amt, sender |-> PublicKey @ PrivateKey[n]]} ELSE ledger[n2]]
    /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] ELSE received[n2] \cup {[h |-> lastHash', prev |-> b, pt |-> "send", amt |-> amt, sender |-> PublicKey @ PrivateKey[n]]}]

CreateOpenBlock(n, b) ==
    /\ b \in BlockDom(NoHash)
    /\ NoHashVal \notin {r.h : r \in ledger[n]}
    /\ ~\E t \in Transaction: t.h = b
    /\ LastHashVal \notin {r.h : r \in ledger[n]}
    /\ b # NoHash
    /\ \E r \in BlockDom(NoHash) : r.h = b /\ r.pt = "send" /\ r.sender = PublicKey @ PrivateKey[n]
    /\ lastHash' = CalculateHash([h |-> b, pt |-> "open", amt |-> 0, sender |-> NoBlock])
    /\ ledger' = [n2 \in Node |-> IF n2 = n THEN ledger[n] \cup {[h |-> lastHash', prev |-> b, pt |-> "open", amt |-> 0, sender |-> NoBlock]} ELSE ledger[n2]]
    /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] ELSE received[n2] \cup {[h |-> lastHash', prev |-> b, pt |-> "open", amt |-> 0, sender |-> NoBlock]}]

CreateReceiveBlock(n, b, amt) ==
    /\ b \in BlockDom(NoHash)
    /\ NoHashVal \notin {r.h : r \in ledger[n]}
    /\ ~\E t \in Transaction: t.h = b
    /\ LastHashVal \notin {r.h : r \in ledger[n]}
    /\ b # NoHash
    /\ \E r \in BlockDom(NoHash) : r.h = b /\ r.pt = "send" /\ r.sender \in PublicKey
    /\ lastHash' = CalculateHash([h |-> b, pt |-> "receive", amt |-> amt, sender |-> NoBlock])
    /\ ledger' = [n2 \in Node |-> IF n2 = n THEN ledger[n] \cup {[h |-> lastHash', prev |-> b, pt |-> "receive", amt |-> amt, sender |-> NoBlock]} ELSE ledger[n2]]
    /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] ELSE received[n2] \cup {[h |-> lastHash', prev |-> b, pt |-> "receive", amt |-> amt, sender |-> NoBlock]}]

CreateChangeRepBlock(n) ==
    /\ LastHashVal \notin {r.h : r \in ledger[n]}
    /\ lastHash' = CalculateHash([h |-> NoHash, pt |-> "change", amt |-> 0, sender |-> NoBlock])
    /\ ledger' = [n2 \in Node |-> IF n2 = n THEN ledger[n] \cup {[h |-> lastHash', prev |-> LastHashVal, pt |-> "change", amt |-> 0, sender |-> NoBlock]} ELSE ledger[n2]]
    /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] ELSE received[n2]]

ProcessNode(n, r) ==
    /\ r \in received[n]
    /\ lastHash' = IF r.h \in {rr.h : rr \in BlockDom(b) : b \in BlockDom(NoHash)} THEN lastHash ELSE CalculateHash(r)
    /\ ledger' = [n2 \in Node |-> IF n2 = n THEN ledger[n] \cup {r} ELSE ledger[n2]]
    /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n] \ {r} ELSE received[n2]]

Next ==
    \/ \E n \in Node : CreateGenesisBlock(n) \/ CreateChangeRepBlock(n)
    \/ \E n \in Node, b \in Hash, amt \in 1..GenesisBalance : CreateSendBlock(n, b, amt)
    \/ \E n \in Node, b \in Hash : CreateOpenBlock(n, b)
    \/ \E n \in Node, b \in Hash, amt \in 1..GenesisBalance : CreateReceiveBlock(n, b, amt)
    \/ \E n \in Node, r \in received[n] : ProcessNode(n, r)

Spec == Init /\ [][Next]_vars

\* the balance invariant is separate from the signature invariant but belongs in the same safety check
BalanceInvariant == TotalBalance(Node) <= GenesisBalance

====