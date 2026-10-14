import json,os,subprocess,sys,tempfile,time
from pathlib import Path
root=Path.cwd();wrapper=root/'scripts/bounded-check.py'
with tempfile.TemporaryDirectory() as temp:
 p=Path(temp)
 for label,code,expected in [('pass','print(123)',0),('fail','raise SystemExit(7)',7),('timeout','import time;time.sleep(30)',124)]:
  receipt=p/(label+'.json');out=subprocess.run([sys.executable,str(wrapper),'--seconds','3','--receipt',str(receipt),'--',sys.executable,'-c',code],capture_output=True,text=True,timeout=5)
  assert out.returncode==expected,(label,out.stdout,out.stderr)
  data=json.loads(receipt.read_text());assert data['elapsedSeconds']<3,data
  print(label,data['status'],round(data['elapsedSeconds'],3))
 pidfile=p/'child.pid';receipt=p/'tree.json'
 code=f'''import subprocess,sys,time,signal
signal.signal(signal.SIGTERM,signal.SIG_IGN)
subprocess.Popen([sys.executable,'-c',"import os,signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);open({str(pidfile)!r},'w').write(str(os.getpid()));time.sleep(30)"])
time.sleep(30)
'''
 out=subprocess.run([sys.executable,str(wrapper),'--seconds','3','--receipt',str(receipt),'--',sys.executable,'-c',code],capture_output=True,text=True,timeout=5)
 assert out.returncode==124,(out.stdout,out.stderr)
 pid=int(pidfile.read_text());status=Path(f'/proc/{pid}/stat')
 assert not status.exists() or status.read_text().split()[2]=='Z',f'Live descendant {pid}'
 print('process-tree timeout verified',json.loads(receipt.read_text())['elapsedSeconds'])
 invalid=subprocess.run([sys.executable,str(wrapper),'--seconds','301','--receipt',str(p/'invalid.json'),'--',sys.executable,'-c','pass'],capture_output=True,text=True,timeout=2)
 assert invalid.returncode==2 and not (p/'invalid.json').exists()
 print('invalid budget rejected')
