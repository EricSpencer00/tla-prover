---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  \A,         \AIsa,         \B,         \BIsa,         \C,         \CIsa,
  \D,         \DIsa,         \E,         \EIsa,         \F,         \FIsa,
  \G,         \GIsa,         \H,         \HIsa,         \I,         \IIso,
  \J,         \JIsa,         \K,         \KIsa,         \L,         \LIsa,
  \M,         \MIsa,         \N,         \NIsa,         \O,         \OIsa,
  \P,         \PIsa,         \Q,         \QIsa,         \R,         \RIso,
  \S,         \SIso,         \T,         \TIso,         \U1,        \U2,
  \U3,        \U4,           \V,         \W,           \W1,        \W2,
  \W3,        \W4,           \X,         \Y1,          \Y2,        \Y3,
  \Y4,        \Z,           \Z1,         \Z2,         \Z3,
  inf,        trivial

SPECIFICATION == Init /\ Next

Init == TRUE

Next == FALSE

INVARIANTS == {\E, \F}

PROPERTIES == {\A, \B}

\A == \AIsa

\AIsa == TRUE

\B == \BIsa

\BIsa == TRUE

\C == \CIsa

\CIsa == TRUE

\D == \DIsa

\DIsa == TRUE

\E == \EIsa

\EIsa == TRUE

\F == \FIsa

\FIsa == TRUE

\G == \GIsa

\GIsa == TRUE

\H == \HIsa

\HIsa == TRUE

\I == \IIso

\IIso == TRUE

\J == \JIsa

\JIsa == TRUE

\K == \KIsa

\KIsa == TRUE

\L == \LIsa

\LIsa == TRUE

\M == \MIsa

\MIsa == TRUE

\N == \NIsa

\NIsa == TRUE

\O == \OIsa

\OIsa == TRUE

\P == \PIsa

\PIsa == TRUE

\Q == \QIsa

\QIsa == TRUE

\R == \RIso

\RIso == TRUE

\S == \SIso

\SIso == TRUE

\T == \TIso

\TIso == TRUE

\U1 == TRUE

\U2 == TRUE

\U3 == TRUE

\U4 == TRUE

\V == TRUE

\W == TRUE

\W1 == TRUE

\W2 == TRUE

\W3 == TRUE

\W4 == TRUE

\X == TRUE

\Y1 == TRUE

\Y2 == TRUE

\Y3 == TRUE

\Y4 == TRUE

\Z == TRUE

\Z1 == TRUE

\Z2 == TRUE

\Z3 == TRUE

inf == U1

trivial == \E

====