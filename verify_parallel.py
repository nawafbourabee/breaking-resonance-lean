#!/usr/bin/env python3
"""Compile the local source dependency closure with up to three concurrent Lean jobs."""
import hashlib,json,os,re,subprocess,sys,time
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REUSE=Path(os.environ.get('BREAKING_RESONANCE_LEAN_REUSE','/Users/nawafbou-rabee/Desktop/quenched-parallel-mcmc/formalization/coupled_jacobi'))
LEAN=Path(os.environ.get('BREAKING_RESONANCE_LEAN_BIN',str(REUSE/'.tools/lean-4.34.0-rc2-darwin_aarch64/bin/lean')))
OUT=ROOT/'.lake/build/lib/lean';LOG=ROOT/'.lake/parallel_logs'
LOG.mkdir(parents=True,exist_ok=True)
# Every non-mathlib import is source-local. No sibling project or SLT cache is used.
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join(map(str,[OUT]+sorted((REUSE/'.lake/packages').glob('*/.lake/build/lib/lean'))))
req=[Path(s) for s in sys.argv[1:]] or [Path('BreakingResonance.lean'),Path('AxiomAudit.lean')]
req=[p.relative_to(ROOT) if p.is_absolute() else p for p in req]
deps={}
def visit(p):
 if p in deps:return
 deps[p]=[]
 for name in re.findall(r'^import\s+([A-Za-z0-9_.]+)',(ROOT/p).read_text(),re.M):
  q=Path(name.replace('.','/')+'.lean')
  if (ROOT/q).is_file():deps[p].append(q);visit(q)
  elif name.startswith(('PersistencePays.','BreakingResonance.','SLT.')):
   raise RuntimeError('Missing source dependency: '+name)
for p in req:visit(p)
def compile_one(p):
 dest=OUT/p.with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 start=time.monotonic()
 r=subprocess.run([str(LEAN),'-DautoImplicit=false','-o',str(dest),str(p)],cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 log=LOG/(str(p).replace('/','__')+'.log');log.write_text(r.stdout)
 if r.returncode:dest.unlink(missing_ok=True)
 return {'module':str(p),'exit_code':r.returncode,'seconds':time.monotonic()-start,'log':str(log)}
pending=set(deps);done=set();rebuilt=set();running={};results=[];failed=False
print(f'Checking local closure ({len(deps)} modules); external project caches excluded.',flush=True)
with ThreadPoolExecutor(max_workers=3) as pool:
 while pending or running:
  if not failed:
   progress=True
   while progress:
    progress=False
    for p in sorted(pending):
     if not all(q in done for q in deps[p]):continue
     dest=OUT/p.with_suffix('.olean')
     fresh=dest.exists() and dest.stat().st_mtime_ns>(ROOT/p).stat().st_mtime_ns and not any(q in rebuilt for q in deps[p]) and all((OUT/q.with_suffix('.olean')).stat().st_mtime_ns<dest.stat().st_mtime_ns for q in deps[p])
     if fresh and p not in req:
      done.add(p);pending.remove(p);progress=True
     elif len(running)<3:
      running[pool.submit(compile_one,p)]=p;pending.remove(p);progress=True
  if not running:break
  ready,_=wait(running,return_when=FIRST_COMPLETED)
  for f in ready:
   p=running.pop(f);result=f.result();results.append(result)
   if result['exit_code']:
    failed=True;print('FAILED '+str(p)+'\n'+Path(result['log']).read_text(),flush=True)
   else:
    done.add(p);rebuilt.add(p)
    if p.parts[0]=='BreakingResonance' or len(rebuilt)%10==0:print(f'{len(done)}/{len(deps)}: {p}',flush=True)
summary={'success':not failed and len(done)==len(deps),'total':len(deps),'checked_or_current':len(done),'rebuilt':len(rebuilt),'results':results}
(LOG/'last_run.json').write_text(json.dumps(summary,indent=2)+'\n')
raise SystemExit(0 if summary['success'] else 1)
