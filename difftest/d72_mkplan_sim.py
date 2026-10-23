import json, shutil, os
W='/home/exedev/lazerproof/.claude/worktrees/agent-ab4030d638366f6d6'
S='/tmp/claude-1000/-home-exedev/5a067c7e-69f6-4190-93e6-f7fa504e1337/scratchpad/d72'
os.makedirs(S+'/bin', exist_ok=True)
for src,dst in [(W+'/model/.lake/build/bin/simtest','simtest_lean'),(W+'/model/.lake/build/bin/evaltest','evaltest'),
                (W+'/impl/target/release/simtest_rs','simtest_rs'),(W+'/impl/target/release/osu_eval','osu_eval')]:
    shutil.copy2(src, S+'/bin/'+dst)
p=json.load(open('/home/exedev/lazerproof/data/wip/rust-sim/plan_e0a.json'))
p['out']=S+'/chunks_d72'; p['json_out']=S+'/results_d72.jsonl'
p['env']={'LEAN_SIMTEST':S+'/bin/simtest_lean','RUST_SIMTEST':S+'/bin/simtest_rs'}
for it in p['items']: it['label']=it['label'].replace('e0:','d72:')
json.dump(p, open(S+'/plan_d72.json','w'), indent=1)
print('ok')
