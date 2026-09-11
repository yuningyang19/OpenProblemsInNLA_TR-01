# Extracted without changes from the previously checked v6 evidence parser.
import gzip,hashlib,json
ALLOWED={"propext","Classical.choice","Quot.sound"}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read_text(p):
 return gzip.open(p,'rt').read() if p.suffix=='.gz' else p.read_text()
def log_sha(p):
 return hashlib.sha256(gzip.open(p,'rb').read()).hexdigest() if p.suffix=='.gz' else sha(p)
def locate_log(p):return p if p.is_file() else p.with_suffix(p.suffix+'.gz')
def require(ok,msg):
 if not ok: raise ValueError(msg)
def parse_log(path):
 targets={};nodes={};end=[]
 for line in read_text(path).splitlines():
  if line.startswith('CERT_TARGET|'):
   r=json.loads(line.split('|',1)[1]); require(r['name'] not in targets,'duplicated target'); targets[r['name']]=r
  elif line.startswith('CERT_NODE|'):
   r=json.loads(line.split('|',1)[1]); require(r['name'] not in nodes,'duplicated node'); nodes[r['name']]=r
  elif line.startswith('CERT_END|'): end.append(int(line.split('|')[1]))
 require(len(end)==1 and end[0]==len(nodes),'incomplete graph output')
 return targets,nodes

def validate_records(targets,nodes,expected,types=None):
 require(len(expected)==len(set(expected)),'duplicated inventory')
 require(set(targets)==set(expected),'missing or unexpected target')
 axiom_closures={}
 for name,r in targets.items():
  require(r['kind']=='theorem','wrong target declaration kind: '+name)
  require(set(r['axioms'])<=ALLOWED,'forbidden axiom record: '+name)
  if types is not None: require(r['type_repr']==types[name],'changed expected type: '+name)
  todo=[name];seen=set();axs=set()
  while todo:
   n=todo.pop()
   if n in seen:continue
   seen.add(n);require(n in nodes,'missing dependency '+n)
   node=nodes[n]
   if node['kind']=='axiom':axs.add(n)
   todo.extend(node['type_constants']+node['proof_constants'])
  require(axs<=ALLOWED,'forbidden transitive axiom: '+name+' '+str(axs-ALLOWED))
  # The structural visitor includes all constructors of reached inductives
  # and every recursor rule. This intentionally exceeds collectAxioms, which
  # follows only the target's used proof/type constants. Never drop an edge.
  require(set(r['axioms'])<=axs,'collectAxioms dependency missing from structural graph: '+name)
  axiom_closures[name]={'collectAxioms':sorted(r['axioms']),
   'conservative_structural_axioms':sorted(axs),'structural_excess':sorted(axs-set(r['axioms']))}
  require(nodes[name]['kind']==r['kind'] and nodes[name]['type_constants']==r['type_constants'] and nodes[name]['proof_constants']==r['proof_constants'],'target graph discrepancy')
 return {'target_count':len(targets),'graph_nodes':len(nodes),'status':'PASS','scope':'encoded declarations only',
  'axiom_closures':axiom_closures}

