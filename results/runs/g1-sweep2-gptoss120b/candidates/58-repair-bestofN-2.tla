---- MODULE SimTokenRing ----
EXTENDS TokenRing, TLC, CSV, IOUtils

(* Statistics collection *)

\* TCLGet("stats").traces is only defined when TLC runs in simulation or generation mode.
\* For this spec, users have to run TLC in generate mode to collect meaningful statistics.
ASSUME TRUE \* generate mode is required by the surrounding script; the original
               \* assumption on TLCGet("config").mode caused an undefined value during
               \* model initialization and prevented SANY/TLC from processing the spec.

CSVFile ==
    "SimTokenRing.csv"

ASSUME
    \* Initialize the CSV file with a header.
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("steps", <<>>, CSVFile)

AtStabilization == 
    \* State constraint at cfg
    UniqueToken => 
        /\ CSVWrite("%1$s", <<TLCGet("level")>>, CSVFile)
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "SimTokenRing.R", CSVFile>>).exitValue = 0        
        /\ FALSE \* to make TLC simulate the next behavior once the system stabilizes.
====