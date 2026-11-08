#!/usr/bin/env python3
"""Reject proof-admission and native-evaluation markers in checked Lean sources."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
pattern=re.compile(r'\b(?:sorry|sorryAx|admit|axiom|native_decide|ofReduceBool)\b')
def strip_comments(source):
 out=[];i=0;depth=0
 while i<len(source):
  pair=source[i:i+2]
  if pair=='/-':depth+=1;out.extend('  ');i+=2
  elif depth and pair=='-/':depth-=1;out.extend('  ');i+=2
  elif not depth and pair=='--':
   while i<len(source) and source[i]!='\n':out.append(' ');i+=1
  else:out.append(source[i] if not depth or source[i]=='\n' else ' ');i+=1
 assert depth==0,'Unclosed block comment'
 return ''.join(out)
files=sorted((ROOT/'SupersingularCurves').rglob('*.lean'))+[ROOT/'SupersingularCurves.lean']
for folder in ['Definitions','Theorems','P2M']:
 files+=sorted((ROOT/'vendor/flt'/folder).rglob('*.lean'))
findings=[]
for p in files:
 clean=strip_comments(p.read_text())
 for m in pattern.finditer(clean):
  findings.append({'path':p.relative_to(ROOT).as_posix(),'line':clean.count('\n',0,m.start())+1,'marker':m.group()})
status=json.loads((ROOT/'verification/checkpoint-status.json').read_text())
report={'checkpoint':status['checkpoint'],'lean_files_scanned':len(files),'scope':'Project proof modules, aggregate import, and all vendored Lean modules; nested block and line comments stripped.','forbidden_markers':pattern.pattern,'findings':findings}
(ROOT/'verification/source-scan.json').write_text(json.dumps(report,indent=2)+'\n')
assert not findings,findings
print(f'PASS: {len(files)} project/vendor Lean sources contain no forbidden proof-admission or native-evaluation markers.')
