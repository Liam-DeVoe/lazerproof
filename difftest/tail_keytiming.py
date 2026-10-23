#!/usr/bin/env python3
"""Key-timing classification of disputed slider tails (docs/server-agreement.md, "margin analysis").
For each tail [start-36, start]: held-whole-window | release-inside(ms after window start) | press-inside | release-rounding
(released <0.5 ms before the window: integer-ms rounding could move it inside) | not-held. Needs data/oracle_v2/playable (tail_margin.py)."""
import json, sys, collections, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tail_margin as tm, oracle_vs_server_v2 as ov
import sqlite3
db=sqlite3.connect(ov.DB)
meta={sid:json.loads(js) for sid,js in db.execute("select id,json from scores where status='ok'")}
names=list(ov.FLIP_SCHEDULES)+sorted(f[:-10] for f in os.listdir(ov.OUT) if f.startswith('jitter') and f.endswith('_obj.jsonl'))
res={nm:ov.load_results(nm+'_obj') for nm in names}
def classify(fr,ws,we,kind):
    held_ws=0
    for f in fr:
        if f[0]<=ws: held_ws=f[3]
        else: break
    ev=[]; prev=None
    for f in fr:
        if prev is not None and ws-40<=f[0]<=we:
            if prev[3] and not f[3]: ev.append(('up',f[0]-ws))
            if f[3]&~prev[3]: ev.append(('down',f[0]-ws))
        prev=f
    ups=[t for k,t in ev if k=='up']; downs=[t for k,t in ev if k=='down']
    if held_ws:
        rel=[t for t in ups if t>0]
        return ('held-whole-window' if not rel else 'release-inside(%.2f)'%rel[0]), ev
    # not held at ws
    lastup=max([t for t in ups if t<=0],default=None)
    if downs and any(0<=t<=we-ws for t in downs): return 'press-inside(%.2f)'%min(t for t in downs if t>=0), ev
    if lastup is not None and lastup>-0.5: return 'release-rounding(%.2f)'%lastup, ev
    return 'not-held(lastup %s)'%('%.2f'%lastup if lastup is not None else 'none'), ev
out=collections.defaultdict(collections.Counter)
for sid in sorted(res['catchup']):
    if sid not in meta: continue
    runs={nm:res[nm][sid] for nm in names if sid in res[nm]}
    cat=ov.compare(runs['catchup'],meta[sid])[0]
    if cat in('exact','replay-gap'): continue
    st=ov.flipcheck_one(meta[sid],runs)['status']
    P=json.load(open(os.path.join(ov.OUT, 'playable', '%d.json')%sid)); fr=tm.frames_of(sid)
    obs={}
    for nm,o in runs.items():
        L=o['live']
        if L.get('failed') or 'objres' not in L: continue
        for i,n,t,r in L['objres']: obs.setdefault((i,n,t),set()).add(r)
    cu={(i,n):r for i,n,t,r in runs['catchup']['live']['objres']}
    group='explained' if st.startswith('demonstrated') else 'unexplained'
    if group=='explained':
        cand=[(i,n,t) for (i,n,t),rs in obs.items() if t=='SliderTailCircle' and len(rs)>1]
    else:
        cand=[(i,n,t) for (i,n,t) in obs if t=='SliderTailCircle' and cu.get((i,n))=='IgnoreMiss' and cu.get((i,0)) in ('Great','Ok','Meh')]
    cls=[]
    for i,n,t in cand:
        tn=tm.hx(P['objects'][i]['nested'][n]['start']); c,ev=classify(fr,tn-36,tn,'tail')
        cls.append(c)
        out[group][c.split('(')[0]]+=1
    srv={ov.camel(k):v for k,v in meta[sid]['statistics'].items()}; orc=runs['catchup']['live']['statistics']
    deficit=srv.get('SliderTailHit',0)-orc.get('SliderTailHit',0)
    print(group[:5], sid, ov.modkey(meta[sid].get('mods',[])), 'tail deficit(srv-orc)',deficit, sorted(cls))
print({g:dict(c) for g,c in out.items()})
