"""Exact proof gate: SANY first, then uncached strict TLAPS within one deadline.

Caller must attest the JDK/JAR, complete verifier runtime and source libraries.
This module records concrete commands and artifact hashes, not a success based
on process exit alone. Existing independent TLAPS diagnostics remain unchanged.
"""
import hashlib
import json
import math
from pathlib import Path
import re
import shutil
import tempfile
import time

from . import runner
from . import proof_full_fragment_check as full
from .proof_fragment_check import _code,classify_result

VERSION='sany-strict-tlaps-ladder-v3'
_INFRA=re.compile(r'Cannot find (?:the )?source file|module[^\n]*not found|could not (?:find|load)|ClassNotFound|NoClassDefFound|UnsupportedClassVersion|No such file|Permission denied|unable to access jar|out of memory|OutOfMemory|Exception|Error: Could not|command not found|backend[^\n]*(?:missing|unavailable|not found)',re.I)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def classify_sany(returncode,output,timed_out,module):
    if timed_out:return 'unmeasured_timeout'
    diagnostic=output
    # SANY deliberately uses this exact exception for ordinary parser aborts.
    # Preserve every other exception/infrastructure signature, even alongside it.
    known_abort=(re.search(r'^(?:\*\*\*)?\s*(?:Parse|Lexical) Error',output,re.I|re.M) and
            re.search(r'^tla2sany\.semantic\.AbortException\s*$',output,re.M) and
            re.search(r'^Could not parse module '+re.escape(module)+r' from file '+re.escape(module)+r'\.tla\s*$',output,re.M))
    if known_abort:
        diagnostic=re.sub(r'^tla2sany\.semantic\.AbortException\s*$', '', output, flags=re.M)
    if _INFRA.search(diagnostic):return 'unmeasured_infrastructure'
    if type(returncode) is not int or (returncode not in (0,1) and not (returncode==255 and known_abort)):
        return 'unmeasured_unknown'
    clean=output.replace('Semantic errors detected: 0','')
    if re.search(r'Semantic errors|\*\*\* Errors:\s*[1-9][0-9]*|(?:Parse|Lexical)\s*Error|Fatal errors while parsing',clean,re.I):
        return 'model_sany_reject'
    if returncode!=0:return 'unmeasured_unknown'
    if re.search(r'\b(?:error|errors|fatal|exception|failed|failure)\b',clean,re.I):return 'unmeasured_unknown'
    if re.search(r'^Semantic processing of module '+re.escape(module)+r'\s*$',output,re.M):return 'pass'
    return 'unmeasured_unknown'


def _checked(path,expected):
    raw=Path(path).read_bytes()
    if sha(raw)!=expected:raise ValueError('Exact source/candidate artifact changed')
    return raw


def _audit_tlaps(record,prefix,fragment,suffix,theorem_name,dependencies):
    candidate=prefix+fragment+suffix;expected=sha(candidate.encode())
    path=Path(record['candidate_path']);work=Path(record['workdir'])
    if (record.get('contract_version')!=full.CONTRACT_VERSION or record.get('sha256')!=expected or
            record.get('dependency_sha256')!=dependencies or not {'--strict','--nofp'}.issubset(record.get('command',[])) or
            path.parent.resolve()!=work.resolve() or record['command'][-1]!=path.name or
            Path(record['command'][0]).resolve()!=Path(runner.TLAPM).resolve()):
        raise ValueError('Strict TLAPS provenance does not bind exact input')
    _checked(path,expected)
    if json.loads((work/'input.json').read_text())!=dict(prefix=prefix,fragment=fragment,suffix=suffix,
            theorem_name=theorem_name,contract_version=full.CONTRACT_VERSION):
        raise ValueError('TLAPS raw input changed')
    if (work/'tlapm.log').read_text()!=record['output']:raise ValueError('TLAPS raw log changed')
    for name,value in dependencies.items():_checked(work/name,value)
    if classify_result(record['returncode'],record['output'],record['timed_out'])!=(record['status'],record['proved'],record['total']):
        raise ValueError('TLAPS raw outcome classification differs')
    if json.loads((work/'result.json').read_text())!=record:raise ValueError('TLAPS saved result differs')


def certify_fragment(prefix,fragment,suffix,*,theorem_name,dependencies=(),work_root,timeout=30,
                     run_command=None,tlaps_checker=None,clock=None):
    if type(timeout) not in (int,float) or not math.isfinite(timeout) or not 0<timeout<=30:
        raise ValueError('One positive finite deadline of at most30 seconds required')
    clock=clock or time.monotonic;run_command=run_command or runner.run_cmd
    tlaps_checker=tlaps_checker or full.certify_fragment
    started=clock();root=Path(work_root).resolve();root.mkdir(parents=True,exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='proof-ladder-',dir=root));candidate=(prefix+fragment+suffix).encode()
    result=dict(contract_version=VERSION,certified=False,status='contract_reject',reason='',workdir=str(work),
        sha256=sha(candidate),timeout_seconds=timeout,seconds=0.,tlaps=None,
        sany=dict(status='not_run',command=None,returncode=None,output='',seconds=0.,timed_out=False))
    (work/'input.json').write_text(json.dumps(dict(prefix=prefix,fragment=fragment,suffix=suffix,
        theorem_name=theorem_name,contract_version=VERSION),indent=2))
    (work/'sany.log').write_text('')
    try:
        name=full.validate_fragment(prefix,fragment,suffix,theorem_name)
        path=work/(name+'.tla');path.write_bytes(candidate);result['candidate_path']=str(path)
        seen={path.name};hashes={};sources={};copies=[]
        for dependency in dependencies:
            dependency=Path(dependency)
            if dependency.suffix!='.tla' or dependency.name in seen:raise ValueError('Duplicate or non-TLA dependency')
            raw=dependency.read_bytes()
            if re.search(r'\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION|AXIOM)\b',_code(raw.decode())):
                raise ValueError('Custom dependency exports unverified theorem or axiom declarations')
            seen.add(dependency.name);hashes[dependency.name]=sha(raw);sources[str(dependency.resolve())]=sha(raw)
            copy=work/dependency.name;copy.write_bytes(raw);copies.append(copy)
        result.update(dependency_sha256=hashes,dependency_source_sha256=sources)
        java=shutil.which('java')
        if not java:raise OSError('Java executable unavailable')
        java=str(Path(java).resolve());jar=Path(runner.TLA2TOOLS).resolve();tmp=work/'jtmp';tmp.mkdir()
        if Path(runner.CLASSPATH).resolve()!=jar:
            raise OSError('SANY classpath differs from pinned tla2tools JAR')
        cmd=[java,'-Djava.io.tmpdir='+str(tmp),'-DTLA-Library='+runner.TLA_LIBRARY,
             '-cp',runner.CLASSPATH,'tla2sany.SANY',path.name]
        result['sany'].update(command=cmd,java_path=java,java_executable_sha256=sha(Path(java).read_bytes()),
            jar_path=str(jar),jar_sha256=sha(jar.read_bytes()),library_path=runner.TLA_LIBRARY)
        remaining=timeout-(clock()-started)
        if remaining<=0:
            result['sany']['status']='unmeasured_budget';result['status']='unmeasured_budget'
            return result
        rc,out,elapsed,timed_out=run_command(cmd,work,remaining)
        status=classify_sany(rc,out,timed_out,name)
        result['sany'].update(status=status,returncode=rc,output=out,seconds=elapsed,timed_out=timed_out)
        (work/'sany.log').write_text(out)
        _checked(path,result['sha256'])
        for source,value in sources.items():_checked(source,value)
        for dep in copies:_checked(dep,hashes[dep.name])
        if status!='pass':result['status']=status;return result
        remaining=timeout-(clock()-started)
        if remaining<=0:result['status']='unmeasured_budget';return result
        _checked(path,result['sha256'])
        for source,value in sources.items():_checked(source,value)
        for dep in copies:_checked(dep,hashes[dep.name])
        record=tlaps_checker(prefix,fragment,suffix,theorem_name=theorem_name,
            dependencies=tuple(copies),work_root=work/'tlaps',timeout=remaining)
        result['tlaps']=record
        _audit_tlaps(record,prefix,fragment,suffix,theorem_name,hashes)
        _checked(path,result['sha256'])
        for source,value in sources.items():_checked(source,value)
        if clock()-started>timeout:result['status']='unmeasured_budget';return result
        from tools.proof_outcome_audit import classify_outcome
        diagnostic=classify_outcome(record,provenance_verified=True)
        result['tlaps_diagnostic']=diagnostic
        result['certified']=(diagnostic['classification']=='proof_success' and
            record.get('certified') is True and record['status']=='pass' and record['proved']==record['total']>0)
        result['status']='pass' if result['certified'] else 'tlaps_not_certified'
        if not result['certified']:result['status']=diagnostic['classification']
    except (OSError,RuntimeError) as exc:
        result.update(status='unmeasured_infrastructure',certified=False,reason=str(exc))
    except (ValueError,KeyError,TypeError) as exc:
        result.update(status='contract_reject' if result['sany']['status']=='not_run' else 'unmeasured_provenance',certified=False,reason=str(exc))
    except Exception as exc:
        result.update(status='unmeasured_unknown',certified=False,reason=type(exc).__name__+': '+str(exc))
    finally:
        result['seconds']=clock()-started
        (work/'result.json').write_text(json.dumps(result,indent=2))
    return result
