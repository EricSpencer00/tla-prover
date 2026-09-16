"""One-response exact saved-logsoftmax CPU offload; no model/optimizer changes.

Only backward-saved full-vocabulary FP32 vectors are transferred. Selected
scalar views in the scorer still retain their storage until its final stack;
this is not a forward-peak or optimizer-memory guarantee. Transfers are
synchronous, unpinned and exact. No CUDA feasibility is inferred from CPU tests.
"""
MAX_HOST_BYTES=1024**3
SCHEMA='saved_logprob_offload_v1'


class LogprobOffload:
    def __init__(self,vocab_size,response_tokens,*,allow_cpu=False):
        if type(vocab_size) is not int or vocab_size<1 or type(response_tokens) is not int or response_tokens<1:
            raise ValueError('Positive integer vocabulary and response length required')
        if type(allow_cpu) is not bool:raise ValueError('Explicit boolean CPU test mode required')
        if vocab_size*response_tokens*4>MAX_HOST_BYTES:raise ValueError('Host copy budget exceeds 1 GiB')
        self.vocab_size=vocab_size;self.response_tokens=response_tokens;self.allow_cpu=allow_cpu
        self.entered=False;self.closed=False;self.failed=False;self.hooks=None
        self.entries={};self.identities={};self.target_pack_calls=0;self.resident_pack_calls=0

    def __enter__(self):
        import torch
        if self.entered:raise ValueError('One context per response; reuse forbidden')
        self.entered=True
        self.hooks=torch.autograd.graph.saved_tensors_hooks(self._pack,self._unpack)
        self.hooks.__enter__();return self

    def __exit__(self,exc_type,exc,tb):
        self.closed=True;self.failed=exc_type is not None
        # The hook object holds bound methods back to this context. Drop our
        # reference so completed response graphs do not require cyclic GC to
        # release their CPU copies. Autograd retains unpack as long as needed.
        hooks=self.hooks;self.hooks=None
        return hooks.__exit__(exc_type,exc,tb)

    def _pack(self,tensor):
        import torch
        from torch.multiprocessing.reductions import StorageWeakRef
        if not self.entered or self.closed:raise ValueError('Pack outside response context')
        target=(tensor.ndim==1 and tensor.dtype==torch.float32 and tensor.numel()==self.vocab_size
                and type(tensor.grad_fn).__name__=='LogSoftmaxBackward0')
        if not target:
            self.resident_pack_calls+=1
            # Saved-hook payload must not keep the original graph Tensor alive.
            # Autograd's saved-tensor edges remain intact; this does NOT detach KV.
            return ('resident',tensor.detach())
        if tensor.device.type!='cuda' and not (self.allow_cpu and tensor.device.type=='cpu'):
            raise ValueError('Actual CUDA source required; CPU mode is test-only')
        storage=tensor.untyped_storage()
        if tuple(tensor.stride())!=(1,) or tensor.storage_offset()!=0 or storage.nbytes()!=self.vocab_size*4:
            raise ValueError('Exact contiguous full-vocabulary storage required')
        identity=StorageWeakRef(storage)
        metadata=dict(source_device=str(tensor.device),dtype=str(tensor.dtype),shape=list(tensor.shape),
                      stride=list(tensor.stride()),storage_offset=tensor.storage_offset(),
                      bytes=storage.nbytes(),version=tensor._version,grad_fn=type(tensor.grad_fn).__name__)
        self.target_pack_calls+=1
        if identity in self.identities:
            index=self.identities[identity];entry=self.entries[index]
            if metadata!=entry['metadata']:raise ValueError('Duplicate saved storage version/layout changed')
            entry['pack_calls']+=1
        else:
            index=len(self.entries)
            if index>=self.response_tokens or (index+1)*self.vocab_size*4>MAX_HOST_BYTES:
                raise ValueError('Unexpected unique vocabulary storage or host budget exceeded')
            host=tensor.detach().to(device='cpu',copy=True,non_blocking=False)
            if host.dtype!=tensor.dtype or host.device.type!='cpu' or host.numel()*host.element_size()!=storage.nbytes():
                raise ValueError('Exact CPU copy required')
            self.identities[identity]=index
            self.entries[index]=dict(metadata=metadata,host=host,pack_calls=1,unpack_calls=0,restored_devices=[])
        return ('offloaded',index)

    def _unpack(self,packed):
        if packed[0]=='resident':return packed[1]
        import torch
        if not self.closed or self.failed:raise ValueError('Backward requires successfully closed forward context')
        entry=self.entries[packed[1]];metadata=entry['metadata']
        if entry['unpack_calls']!=0:raise ValueError('Repeated backward/reuse forbidden')
        restored=entry['host'].to(device=metadata['source_device'],non_blocking=False)
        if (str(restored.device)!=metadata['source_device'] or restored.dtype!=torch.float32 or
            list(restored.shape)!=metadata['shape'] or list(restored.stride())!=metadata['stride'] or
            restored.storage_offset()!=0):
            raise ValueError('Restored device/dtype/layout mismatch')
        entry['unpack_calls']+=1;entry['restored_devices'].append(str(restored.device))
        return restored

    def report(self):
        records=[dict(index=index,**entry['metadata'],pack_calls=entry['pack_calls'],
                      unpack_calls=entry['unpack_calls'],restored_devices=list(entry['restored_devices']),
                      host_device=str(entry['host'].device),host_dtype=str(entry['host'].dtype),
                      host_bytes=entry['host'].numel()*entry['host'].element_size())
                 for index,entry in self.entries.items()]
        return dict(schema=SCHEMA,vocab_size=self.vocab_size,response_tokens=self.response_tokens,
                    allow_cpu_test_only=self.allow_cpu,entered=self.entered,closed=self.closed,failed=self.failed,
                    target_pack_calls=self.target_pack_calls,resident_pack_calls=self.resident_pack_calls,
                    unique_storages=len(records),host_bytes=sum(r['host_bytes'] for r in records),
                    unpack_calls=sum(r['unpack_calls'] for r in records),records=records,
                    scope='Exact saved FP32 LogSoftmaxBackward0 vectors only; resident saved tensors keep same storage; no causal KV detach, no optimizer, no CUDA memory certificate')

    def validate(self,stage='forward'):
        report=self.report()
        validate_report(report,vocab_size=self.vocab_size,response_tokens=self.response_tokens,
                        stage=stage,require_cuda=not self.allow_cpu)
        return report


def validate_report(report,*,vocab_size,response_tokens,stage,require_cuda=True):
    if stage not in ('forward','backward'):raise ValueError('Explicit forward/backward stage required')
    if (report.get('schema')!=SCHEMA or report.get('vocab_size')!=vocab_size or
        report.get('response_tokens')!=response_tokens or report.get('entered') is not True or
        report.get('closed') is not True or report.get('failed') is not False or
        (require_cuda and report.get('allow_cpu_test_only') is not False)):
        raise ValueError('Offload context identity/state mismatch')
    records=report.get('records',[])
    expected_bytes=vocab_size*response_tokens*4
    if (len(records)!=response_tokens or report.get('unique_storages')!=response_tokens or
        report.get('host_bytes')!=expected_bytes or expected_bytes>MAX_HOST_BYTES):
        raise ValueError('Offload unique storage/host byte accounting mismatch')
    packs=0;unpacks=0
    for index,row in enumerate(records):
        device=row.get('source_device','')
        actual_cuda=device.startswith('cuda:') and device[5:].isdigit()
        if (not actual_cuda and (require_cuda or device!='cpu')):
            raise ValueError('Source device not admitted')
        expected_unpacks=int(stage=='backward')
        if (row.get('index')!=index or row.get('dtype')!='torch.float32' or
            row.get('shape')!=[vocab_size] or row.get('stride')!=[1] or row.get('storage_offset')!=0 or
            row.get('bytes')!=vocab_size*4 or row.get('grad_fn')!='LogSoftmaxBackward0' or
            type(row.get('version')) is not int or row['version']<0 or
            type(row.get('pack_calls')) is not int or row['pack_calls']<1 or
            row.get('unpack_calls')!=expected_unpacks or
            row.get('restored_devices')!=([device] if expected_unpacks else []) or
            row.get('host_device')!='cpu' or row.get('host_dtype')!='torch.float32' or
            row.get('host_bytes')!=vocab_size*4):
            raise ValueError('Saved/restored storage evidence mismatch')
        packs+=row['pack_calls'];unpacks+=row['unpack_calls']
    if report.get('target_pack_calls')!=packs or report.get('unpack_calls')!=unpacks:
        raise ValueError('Offload counter accounting mismatch')
    if type(report.get('resident_pack_calls')) is not int or report['resident_pack_calls']<0:
        raise ValueError('Resident accounting invalid')
    return report
