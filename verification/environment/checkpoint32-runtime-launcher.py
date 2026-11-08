#!/usr/bin/env python3
import os,sys,fcntl
real='/workspace/scratch/8cf314e8ad34/checkpoint32-restoration/runtime/lean-4.34.0-rc2-linux/bin/lean.bin'
if any(a.endswith('.lean') for a in sys.argv[1:]):
 import time
 locks=[open('/workspace/scratch/8cf314e8ad34/checkpoint32-restoration/compiler-'+str(i)+'.lock','w') for i in range(1)]
 found=False
 while not found:
  for f in locks:
   try:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
   except BlockingIOError:continue
   os.set_inheritable(f.fileno(),True)
   found=True
   break
  if not found:time.sleep(.1)
 extra=[]
 from pathlib import Path
 for a in sys.argv[1:]:
  if '/SupersingularCurves/Geometry/' in a and a.endswith('.lean') and Path(a).stem in ['ScalarFrobeniusTatePolarizedGraph','AbelianVerschiebungBinaryProducts']:
   snap=Path('/workspace/scratch/8cf314e8ad34/checkpoint32-restoration/headers')/(Path(a).stem+'.snap')
   extra=['--incr-load='+str(snap)] if snap.exists() else ['--incr-header-save='+str(snap)]
 os.execv(real,[real,'-j1','-DElab.async=false',*extra,*sys.argv[1:]])
os.execv(real,[real,*sys.argv[1:]])
