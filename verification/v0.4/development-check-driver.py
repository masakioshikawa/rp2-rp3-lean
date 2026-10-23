from pathlib import Path
import datetime as dt
import fcntl, hashlib, importlib.util, json, os, shutil, subprocess, time

here=Path(__file__).resolve().parent
root=here/'project'
out=root/'verification/v0.4'
out.mkdir(exist_ok=True)
spec=importlib.util.spec_from_file_location('v',root/'scripts/verify.py')
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
env=dict(os.environ,LEAN_NUM_THREADS='1')
env['PATH']='/workspace/scratch/a56cdf22748d/toolchains/lean-4.34.1-linux/bin:'+env['PATH']
env['LD_PRELOAD']='/workspace/scratch/a56cdf22748d/toolchains/proc-self-compat.so'
snapshot=json.loads((root/'verification/v0.4-source-snapshot.json').read_text())
assert v.snapshot()==snapshot['sources']
base=here.parent/'rp2-strengthening/project'
modules=v.modules_in_order()
changed=[str(p) for _,p in modules if not (base/p).exists() or v.sha256(base/p)!=v.sha256(root/p)]
summary={'started_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
 'result':'running','validation_mode':'fresh default-elaboration standalone compilation and raw proof-dependency check; not a separate full audit',
 'module_count':len(modules),'new_or_changed_modules':changed,'source_sha256':v.snapshot(),
 'prior_v031_archive_sha256':'9131bf5589e158621e47df273aef0367f6b355f2fbc1d2cb139a308c0b99a32b',
 'check_program_sha256':v.sha256(root/'verification/CheckPublicUnion.lean'),
 'commands':[]}
def save(): (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
save()
def run(label,cmd):
 start=time.monotonic()
 print('START '+label,flush=True)
 with (out/(label+'.log')).open('w') as log:
  p=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=1200)
 summary['commands'].append({'label':label,'command':cmd,'exit_code':p.returncode,
  'elapsed_seconds':round(time.monotonic()-start,3),'log':label+'.log','log_sha256':v.sha256(out/(label+'.log'))})
 save()
 print('END '+label+': '+str(p.returncode),flush=True)
 if p.returncode:
  summary['result']='failed';save();raise SystemExit(p.returncode)
 return (out/(label+'.log')).read_text()
print('Waiting for ongoing standalone compilation.',flush=True)
with (here/'compiler.lock').open('w') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 # The parent checks the compilation process exit status separately. This
 # check also requires a freshly generated object for the current source.
 obj=root/'.lake/build/lib/lean/RP2-Formalization.olean'
 assert obj.is_file() and obj.stat().st_mtime>=(root/'RP2-Formalization.lean').stat().st_mtime
 standalone_log=here/'compile-logs/RP2-Formalization.log'
 assert 'error:' not in standalone_log.read_text()
 shutil.copy2(standalone_log,out/'standalone-default.log')
 summary['standalone']={'command':['lake','env','lean','-j1','-o','.lake/build/lib/lean/RP2-Formalization.olean','RP2-Formalization.lean'],
  'source_sha256':v.sha256(root/'RP2-Formalization.lean'),'object_sha256':v.sha256(obj),
  'log':'standalone-default.log','log_sha256':v.sha256(out/'standalone-default.log')}
 save()
 pins=v.check_configuration()
 for name,rev in pins['packages'].items():
  actual=subprocess.check_output(['git','-C',str(root/'.lake/packages'/name),'rev-parse','HEAD'],text=True).strip()
  dirty=subprocess.check_output(['git','-C',str(root/'.lake/packages'/name),'status','--porcelain','--untracked-files=all'],text=True).strip()
  assert actual==rev and not dirty,(name,actual,dirty)
 summary['dependency_revisions']=pins['packages']
 run('bundle-freshness',['python3','bundle.py','--check'])
 run('semantic-witnesses',['lake','env','lean','-j1','SemanticWitnesses.lean'])
 run('principal-statements-and-axioms',['lake','env','lean','-j1','AxiomAudit.lean'])
 text=run('public-dependencies',['lake','env','lean','-j1','--run','verification/CheckPublicUnion.lean'])
 assert 'DEPENDENCY_AUDIT_SUCCESS' in text
 summary['public_root_count']=sum(line.startswith('ROOT\t') for line in text.splitlines())
 summary['dependency_count']=int(next(line.split('\t')[1] for line in text.splitlines() if line.startswith('PUBLIC_CLOSURE\t')))
 summary['axioms']=[line.split('\t')[1] for line in text.splitlines() if line.startswith('AXIOM\t')]
 assert set(summary['axioms'])=={'propext','Classical.choice','Quot.sound'}
 assert v.snapshot()==snapshot['sources']
 compiled=out/'module-compilation'
 compiled.mkdir(exist_ok=True)
 for name,p in modules:
  log=here/'compile-logs'/(name+'.log')
  if log.exists():
   assert 'error:' not in log.read_text(),name
   shutil.copy2(log,compiled/log.name)
 summary['result']='passed'
 summary['completed_utc']=dt.datetime.now(dt.timezone.utc).isoformat()
 save()
 print('FINAL_COMPILATION_CHECKS_PASSED',flush=True)
