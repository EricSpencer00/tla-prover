"""Bounded subprocess execution with tracked-descendant cleanup.

Polling is not kernel containment: an instantaneous double-fork can escape
discovery. Only ancestry-observed PID/creation-time identities are signalled;
no executable-name or global-user-process cleanup is performed.
"""
import os
import selectors
import signal
import subprocess
import time

import psutil


def same_process(pid,created):
    try:
        process=psutil.Process(pid)
        return process if process.create_time()==created and process.is_running() else None
    except psutil.NoSuchProcess:return None


class Ownership:
    def __init__(self,pid):
        process=psutil.Process(pid)
        self.owned={pid:process.create_time()};self.groups={pid:os.getpgid(pid)};self.errors=[];self.signals=[]

    def scan(self):
        for pid,created in list(self.owned.items()):
            try:
                process=same_process(pid,created)
                if process is None:continue
                self.groups[pid]=os.getpgid(pid)
                for child in process.children(recursive=True):
                    created=child.create_time()
                    if child.pid in self.owned and self.owned[child.pid]!=created:
                        self.errors.append('owned_pid_reused:'+str(child.pid));continue
                    self.owned.setdefault(child.pid,created);self.groups[child.pid]=os.getpgid(child.pid)
            except (psutil.NoSuchProcess,ProcessLookupError):pass
            except psutil.AccessDenied as exc:self.errors.append('tracking_access_denied:'+str(exc.pid))

    def alive(self):
        result=[]
        for pid,created in self.owned.items():
            try:
                process=same_process(pid,created)
                if process is not None and process.status()!=psutil.STATUS_ZOMBIE:result.append((pid,created))
            except psutil.NoSuchProcess:pass
            except psutil.AccessDenied:self.errors.append('identity_access_denied:'+str(pid))
        return result

    def terminate(self):
        """Signal exact owned identities, including detached session leaders.

        Individual signalling avoids killing unrelated members of a group an
        owned process joined. Repeated scans capture children before their
        parent disappears; the initial root group is not blindly swept.
        """
        self.scan()
        for pid,created in reversed(self.alive()):
            try:
                process=same_process(pid,created)
                if process is not None:
                    # psutil's send_signal rechecks process identity internally.
                    process.send_signal(signal.SIGKILL)
                    self.signals.append(dict(pid=pid,created=created,signal='SIGKILL'))
            except psutil.NoSuchProcess:pass
            except (psutil.AccessDenied,PermissionError):self.errors.append('signal_denied:'+str(pid))


def run_owned(cmd,cwd,timeout,*,poll_interval=.02,cleanup_reserve=.5,max_output_bytes=16*1024*1024):
    """Return execution, ownership and bounded-output evidence, never proof truth."""
    if not 0<timeout or not 0<poll_interval<=.1 or not 0<cleanup_reserve or max_output_bytes<1:
        raise ValueError('Positive execution, polling, cleanup and output budgets required')
    import math
    if not all(math.isfinite(v) for v in (timeout,poll_interval,cleanup_reserve)):
        raise ValueError('Finite budgets required')
    start=time.monotonic();deadline=start+timeout;reserve=min(cleanup_reserve,timeout/4)
    process=subprocess.Popen(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
    selector=None
    try:
        tracker=Ownership(process.pid);selector=selectors.DefaultSelector()
        os.set_blocking(process.stdout.fileno(),False);selector.register(process.stdout,selectors.EVENT_READ)
    except BaseException as exc:
        # This direct child has not been reaped, so its PID cannot be reused.
        try:
            if process.poll() is None:process.kill()
        except ProcessLookupError:pass
        try:process.wait(timeout=max(0,deadline-time.monotonic()))
        except subprocess.TimeoutExpired:pass
        finally:
            process.stdout.close()
            if selector is not None:selector.close()
        if not isinstance(exc,Exception):raise
        elapsed=time.monotonic()-start
        return dict(command=list(cmd),cwd=str(cwd),root_pid=process.pid,returncode=process.returncode,
            output='',seconds=elapsed,timed_out=elapsed>timeout,output_complete=False,output_limit=False,
            cleanup_complete=False,surviving_owned_processes=[],owned_processes=[],signals=[],
            root_reaped=process.poll() is not None,errors=['ownership_initialization_failed:'+type(exc).__name__+': '+str(exc)],
            execution_complete=False,containment='Ownership initialization failed; descendants were not established')
    chunks=[];size=0;eof=False;timed_out=False;output_limit=False;cleaning=False;interrupted=None
    try:
        while time.monotonic()<deadline:
            tracker.scan();rc=process.poll()
            if rc is not None or time.monotonic()>=deadline-reserve or output_limit:
                if rc is None and not output_limit:timed_out=True
                cleaning=True;tracker.terminate()
            if eof and rc is not None and not tracker.alive():break
            for key,_ in selector.select(min(poll_interval,max(0,deadline-time.monotonic()))):
                try:data=os.read(key.fd,65536)
                except BlockingIOError:continue
                if not data:
                    eof=True;selector.unregister(key.fileobj);continue
                available=max_output_bytes-size
                chunks.append(data[:available]);size+=min(available,len(data))
                if len(data)>available:output_limit=True
        if process.poll() is None or tracker.alive():tracker.terminate()
        remaining=max(0,deadline-time.monotonic())
        try:process.wait(timeout=remaining)
        except subprocess.TimeoutExpired:pass
    except BaseException as exc:
        interrupted=exc;tracker.terminate()
        try:process.wait(timeout=max(0,deadline-time.monotonic()))
        except subprocess.TimeoutExpired:pass
    finally:
        selector.close();process.stdout.close()
    survivors=tracker.alive();complete=not survivors and process.poll() is not None and not tracker.errors
    elapsed=time.monotonic()-start;timed_out=timed_out or elapsed>timeout
    result=dict(command=list(cmd),cwd=str(cwd),root_pid=process.pid,root_reaped=process.poll() is not None,returncode=process.returncode,
        output=b''.join(chunks).decode('utf-8',errors='replace'),seconds=elapsed,
        timed_out=timed_out,output_complete=eof and not output_limit,output_limit=output_limit,
        cleanup_complete=complete,surviving_owned_processes=[dict(pid=p,created=c) for p,c in survivors],
        owned_processes=[dict(pid=p,created=c,pgid=tracker.groups.get(p)) for p,c in tracker.owned.items()],signals=tracker.signals,
        errors=tracker.errors,execution_complete=complete and eof and not output_limit and not timed_out,
        containment='Best-effort ancestry polling; instantaneous unobserved reparenting is not excluded')
    if interrupted is not None:raise interrupted
    return result


def as_runner_tuple(result):
    """Incomplete cleanup/output can never look like a successful rc0 command."""
    valid=(result['execution_complete'] and result['cleanup_complete'] and result['output_complete']
           and not result['timed_out'] and not result.get('output_limit',False))
    return (result['returncode'] if valid else -1,result['output'],result['seconds'],
            result['timed_out'] or not valid)
