import json
S='/tmp/claude-1000/-home-exedev/5a067c7e-69f6-4190-93e6-f7fa504e1337/scratchpad/d72'
D='/home/exedev/lazerproof/data/wip'
p={'out':S+'/chunks_e72','json_out':S+'/results_e72.jsonl',
   'env':{'LEAN_EVALTEST':S+'/bin/evaltest','RUST_EVAL':S+'/bin/osu_eval'},
   'items':[
    {'label':'e72:v2:catchup','list':D+'/d49-reg/v2_500.txt','chunk':50,'args':[]},
    {'label':'e72:as','list':D+'/d49-reg/as_eval.txt','chunk':35,'args':['--replace-mods']},
    {'label':'e72:h:jobmods','list':D+'/rust-eval/lists/h_jobmods.txt','chunk':40,'args':['--replace-mods']},
    {'label':'e72:h:rest','list':D+'/rust-eval/lists/h_rest.txt','chunk':40,'args':['--replace-mods']},
    {'label':'e72:stable15','list':D+'/rust-eval/lists/stable_15.txt','chunk':40,'args':[]},
    {'label':'e72:v2:d1','list':D+'/rust-eval/lists/v2_d1.txt','chunk':20,'args':['--schedule','dense1ms']},
    {'label':'e72:v2:pf','list':D+'/rust-eval/lists/v2_pf.txt','chunk':40,'args':['--schedule','perframe']},
   ]}
json.dump(p, open(S+'/plan_e72.json','w'), indent=1)
