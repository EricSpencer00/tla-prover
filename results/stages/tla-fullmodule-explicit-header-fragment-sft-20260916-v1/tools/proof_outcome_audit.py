"""Read-only conservative diagnostic classification; never certify or run TLAPS.

Callers must bind source, candidate/input/dependency bytes, complete raw logs,
and verifier identity before setting provenance_verified=True. Classification
alone does not establish theorem correctness, on-policy sampling or split safety.
reward_eligible means diagnostic suitability only; it never authorizes using
evaluation data, including fresh14, original18, official119 or holdout30 in RL.
"""
import re

MODEL_CLASSES={'proof_success','model_contract','model_parse','model_scope','unproved_obligation'}
CONTRACT_REASONS={
    'fragment must begin a proof',
    'hierarchical steps cannot follow a terminal leaf proof',
    'admission, declaration, or module injection',
    'unsupported hierarchical step structure',
    'unsupported step-local DEFINE syntax',
    'step-local DEFINE shadows an existing name',
    'unsupported DEFINE body or proof boundary',
    'every definition must be a single explicit hierarchical DEFINE step',
    'proof pragmas are outside the full-fragment contract',
}
PARSE=re.compile(r'^\s*tlapm ending abnormally with Failure\("(?:Proof\.Parser(?:\.toplevel)?|Module\.Parser\.parse_file|Expr\.Parser\.WF:2)"\)',re.M)
ASSERTION=re.compile(r'\bAssertion failed\b|\bAssert_failure\b|\bassertion failure\b',re.I)
INTERNAL=re.compile(r'\b(?:Segmentation fault|Stack_overflow|Bus error)\b|Fatal error:\s*exception',re.I)
INFRA=re.compile(r'Executable "[^"\n]+" not found|(?:command not found|No such file or directory|Permission denied|Cannot allocate memory|out of memory|No space left on device)|\b(?:backend|prover|solver)\b[^\n]*(?:timed out|timeout|not found|unavailable)',re.I)
SCOPE=re.compile(r'^Error: Operator "[^"\n]+" not found\s*$',re.M)
FAILED=re.compile(r'^\[ERROR\]: ([0-9]+)/([0-9]+) obligations? failed\.\s*$',re.M)
POSITIVE=re.compile(r'^\s*(?:\[INFO\]: )?All ([0-9]+) obligations? proved\.?\s*$',re.M)


def _hash(value):
    return isinstance(value,str) and re.fullmatch('[0-9a-f]{64}',value) is not None


def _strict_record(row):
    command=row.get('command')
    candidate=row.get('candidate_path')
    return (isinstance(command,list) and all(isinstance(x,str) for x in command)
            and {'--strict','--nofp'}.issubset(command) and isinstance(candidate,str)
            and bool(candidate) and _hash(row.get('sha256')) and
            type(row.get('returncode')) is int and row.get('timed_out') is False)


def classify_outcome(row, *, provenance_verified=False):
    """Known diagnostics only; unknown/nonzero exit codes are not RL negatives."""
    if type(provenance_verified) is not bool:
        raise ValueError('Explicit boolean provenance attestation required')
    def result(kind,reason):
        measured=kind in MODEL_CLASSES and provenance_verified
        return dict(classification=kind,measured_model_outcome=measured,
                    reward_eligible=measured,reason=reason,
                    provenance_verified=provenance_verified)
    if not isinstance(row,dict):return result('unmeasured_unknown','Malformed row')
    output=row.get('output','');reason=row.get('reason','')
    if not isinstance(output,str) or not isinstance(reason,str):
        return result('unmeasured_unknown','Malformed diagnostic text')
    diagnostic=output+'\n'+reason
    # Checker assertions take priority even when another diagnostic resembles
    # a parse failure, an unproved obligation or a positive summary.
    if ASSERTION.search(diagnostic) or INTERNAL.search(diagnostic):
        return result('unmeasured_checker_internal','Checker assertion/internal crash signature')
    if (row.get('timed_out') is True or row.get('status') in {'timeout','infrastructure_error'}
            or (type(row.get('returncode')) is int and row['returncode']<0) or INFRA.search(diagnostic)):
        return result('unmeasured_infrastructure','Timeout, interrupted process or infrastructure diagnostic')
    if row.get('status')=='contract_reject' and row.get('certified') is False:
        if reason in CONTRACT_REASONS and _hash(row.get('sha256')) and not output and row.get('returncode') is None:
            return result('model_contract','Known model-fragment contract rejection')
        return result('unmeasured_unknown','Unrecognized or scaffold/dependency contract rejection')
    if (row.get('status')=='no_proof_fragment' and row.get('certified') is False and
            row.get('fragment') is None and _hash(row.get('raw_reply_sha256'))):
        return result('model_contract','Completed reply contains no extractable proof fragment')
    if not _strict_record(row):
        return result('unmeasured_unknown','Missing complete strict uncached candidate record')
    rc=row['returncode']
    positives=POSITIVE.findall(output)
    if rc==0:
        if (row.get('certified') is True and row.get('status')=='pass' and len(positives)==1
                and type(row.get('proved')) is int and type(row.get('total')) is int
                and row['proved']==row['total']==int(positives[0])>0
                and not re.search(r'\b(?:failed|omitted|interrupted|error|exception)\b',output,re.I)):
            return result('proof_success','Strict rc0 and one positive full-obligation summary agree')
        return result('unmeasured_unknown','rc0 alone or inconsistent positive certification')
    if row.get('certified') is not False or positives:
        return result('unmeasured_unknown','Nonzero exit conflicts with positive certification')
    if re.search(r'Fatal error',output,re.I):
        return result('unmeasured_unknown','Unrecognized fatal diagnostic')
    # These are the exact Failure signatures in immutable fresh14 BASE/child
    # logs, not a broad assumption that every OCaml Failure is a parse error.
    failures=re.findall(r'Failure\("([^"\n]+)"\)',output)
    if PARSE.search(output) and failures and all(f in {
            'Proof.Parser','Proof.Parser.toplevel','Module.Parser.parse_file','Expr.Parser.WF:2'} for f in failures):
        return result('model_parse','Known TLAPM proof/module/WF parser rejection')
    if SCOPE.search(output) and failures and all(f=='Expr.Anon: 4' for f in failures):
        return result('model_scope','Operator-not-found with matching Expr.Anon diagnostic')
    # Search exhaustion is only classified when TLAPS reports a concrete
    # failed-obligation fraction and no unknown fatal/backend diagnostic.
    failed=FAILED.findall(output)
    backend_errors=[line for line in output.splitlines() if re.match(r'(?i)^\w+ error:',line)]
    if (rc==10 and len(failed)==1 and 0<int(failed[0][0])<=int(failed[0][1]) and
            '[ERROR]: Could not prove or check:' in output and not failures and
            not re.search(r'ending abnormally|Fatal error|exception',output,re.I) and
            not re.search(r'^\s*Error:',output,re.M|re.I) and
            all(line=='Zenon error: exhausted search space without finding a proof' for line in backend_errors)):
        return result('unproved_obligation','Completed strict run reports concrete unproved obligations')
    return result('unmeasured_unknown','No established model-error diagnostic; exit code is insufficient')
