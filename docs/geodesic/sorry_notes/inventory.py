#!/usr/bin/env python3
"""Per-declaration proved/open inventory of the Geodesic modules (run from the repo root)."""
import re
order=['FlowInterface','FlowInterface/OrbitExtension','GeometricData','EffectiveData','OrbitData',
       'Localization','BracketApprox/Geometry','BracketApprox','PlaqueNeighborhoods',
       'SectionReconstruction','OrbitToLocation','UpperBound/Returns','UpperBound/PrecisionChain',
       'UpperBound/SectionPoint','UpperBound/Mixed','UpperBound']
head=r'^(theorem|lemma|def|noncomputable def|structure|inductive|abbrev|/--|/-!|end |namespace |section |omit |include |variable )'
tot_s=tot_d=0
for f in order:
    lines=open(f'KolmogorovMathlib/PointToSet/Geodesic/{f}.lean',encoding='utf-8').read().splitlines()
    decls=[];i=0
    while i<len(lines):
        m=re.match(r'^(theorem|lemma|def|noncomputable def|structure|inductive|abbrev) (\S+)',lines[i])
        if m:
            kind=m.group(1).replace('noncomputable ','');name=m.group(2);j=i+1
            while j<len(lines) and not re.match(head,lines[j]): j+=1
            st='open' if re.search(r'\bsorry\b','\n'.join(lines[i:j])) else 'ok'
            decls.append((kind,name,st));i=j
        else: i+=1
    n_open=sum(1 for d in decls if d[2]=='open');tot_s+=n_open;tot_d+=len(decls)
    print(f'| {f} | {len(decls)} | {n_open} | '+', '.join(f'`{n}`' for k,n,st in decls if st=='open')+' |')
print(f'TOTAL {tot_d} declarations, {tot_s} open')
