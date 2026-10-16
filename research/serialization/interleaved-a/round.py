from pathlib import Path
import subprocess,json,time,hashlib,shutil,os,random,select
root=Path(__file__).parent;start=time.monotonic();rows=[];frozen=root;seed=20261023
for name in ['a','baseline']:
 for suffix in ['-copy']:shutil.copyfile(frozen/f'{name}-both.mjs',root/f'{name}{suffix}-both.mjs')
 assert (root/f'{name}-both.mjs').read_bytes()==(root/f'{name}-copy-both.mjs').read_bytes()
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
scenarios=['numeric-10k','undefined-10k','mixed-10k','records-small','records-1k','records-10k','dag-2k','dense-dag','cycle-300','deep-200','deep-2000','collections','dates-2k','rich','views-shared','binary-1m','url-linked','temporal-exact','hole-first','hole-last','strings-10k','scalar-boundaries']
allowed=sorted(os.sched_getaffinity(0));pin=4 if 4 in allowed and shutil.which('taskset') else None
jobs=[(scenario,rep)for scenario in scenarios for rep in range(2)];random.Random(seed).shuffle(jobs)
manifest={'seed':seed,'clusterOrder':jobs,'allowedCPUs':allowed,'workerPinnedCPU':pin,'cpuMax':Path('/sys/fs/cgroup/cpu.max').read_text().strip(),'warmupSegments':3,'warmupSegmentMs':50,'timedBlocks':6,'blockMs':40,'WilliamsRows':[[0,1,3,2],[1,2,0,3],[2,3,1,0],[3,0,2,1]],'independentClustersPerFixture':2,'isolatedArmsPerCluster':4,'copiesEqual':True,'acceptance':'Target gain in both independent clusters beyond exact-control variation. Rest slowdowns unresolved against controls are NOT unconditional passes. Unstable controls mean unsuitable evidence; no retry loop.','hashes':{p.name:sha(p)for p in root.glob('*.mjs')}}
(root/'manifest.json').write_text(json.dumps(manifest,indent=2))
pending={}
def receive(child):
 buffer=pending.get(child.pid,b'')
 while b'\n' not in buffer:
  remaining=285-(time.monotonic()-start)
  if remaining<=0 or not select.select([child.stdout],[],[],remaining)[0]:raise TimeoutError('Worker IPC exceeded whole-round deadline')
  chunk=os.read(child.stdout.fileno(),65536)
  if not chunk:raise RuntimeError('Worker stdout closed; exit status '+str(child.poll()))
  buffer+=chunk
 line,_,pending[child.pid]=buffer.partition(b'\n')
 return json.loads(line)
def request(child,command):
 if time.monotonic()-start>=285:raise RuntimeError('Incomplete bounded round')
 child.stdin.write(json.dumps(command)+'\n');child.stdin.flush();return receive(child)
for number,(scenario,rep)in enumerate(jobs):
 children={};ready={};warmups=[];blocks=[];clusterStart=time.monotonic();fixtureSeed=seed+scenarios.index(scenario)*1009
 names=['a','a-copy','baseline','baseline-copy'];spawnOrder=names.copy();random.Random(fixtureSeed+rep*97).shuffle(spawnOrder)
 try:
  for name in spawnOrder:
   args=['node','--harmony-temporal','--expose-gc',str(root/'worker.mjs'),name,scenario]
   if pin is not None:args=['taskset','-c',str(pin),*args]
   child=subprocess.Popen(args,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,bufsize=1);children[name]=child;ready[name]=receive(child)
   assert ready[name]['ready'] and ready[name]['fidelity']=='pass'
  assert ready['a']['payload']==ready['a-copy']['payload'] and ready['baseline']['payload']==ready['baseline-copy']['payload']
  startupMs=(time.monotonic()-clusterStart)*1000
  ops=['encode','decode','roundtrip'];random.Random(fixtureSeed^0x613feb).shuffle(ops)
  for op in ops:
   order=names.copy();random.Random(fixtureSeed+['encode','decode','roundtrip'].index(op)*7919).shuffle(order)
   for segment in range(3):
    for position in range(4):
     name=order[(position+segment+rep*2)%4];warmups.append(request(children[name],dict(op=op,phase='warmup',segment=segment,position=position,ms=50)))
   for block in range(6):
    williams=[[0,1,3,2],[1,2,0,3],[2,3,1,0],[3,0,2,1]][(rep*6+block)%4]
    actualOrder=[order[i]for i in williams]
    for position,name in enumerate(actualOrder):
     blocks.append(request(children[name],dict(op=op,phase='timed',block=block,position=position,order=actualOrder,ms=40)))
  shutdown={}
  for name,child in children.items():
   shutdown[name]=request(child,{'exit':True});assert shutdown[name]['done'];child.wait(timeout=5)
  rows.append(dict(scenario=scenario,rep=rep,fixtureSeed=fixtureSeed,spawnOrder=spawnOrder,opOrder=ops,ready=ready,shutdown=shutdown,warmups=warmups,blocks=blocks,startupMs=startupMs,totalWallMs=(time.monotonic()-clusterStart)*1000))
  (root/'samples.json').write_text(json.dumps(rows,indent=2))
 finally:
  for child in children.values():
   if child.poll()is None:child.terminate()
  for child in children.values():
   if child.poll()is None:
    try:child.wait(timeout=2)
    except subprocess.TimeoutExpired:child.kill();child.wait()
 if(number+1)%11==0:print('completed clusters',number+1,'of',len(jobs),flush=True)
assert all(sha(root/name)==digest for name,digest in manifest['hashes'].items())
print(json.dumps({'clusters':len(rows),'childProcesses':len(rows)*4,'blockObservations':sum(len(r['blocks'])for r in rows),'elapsedSeconds':time.monotonic()-start}))
