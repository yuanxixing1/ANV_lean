#!/usr/bin/env python3
"""Exhaustively rebuild and audit the delivered project; standard-library Python only."""
import datetime, hashlib, json, os, pathlib, re, shlex, shutil, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parent.parent
OUT=ROOT/'verification'
OUT.mkdir(exist_ok=True)
# A failed rerun must never leave an older PASS marker in place.
if (OUT/'RESULT.txt').exists(): (OUT/'RESULT.txt').unlink()
os.chdir(ROOT)
os.environ['LEAN_NUM_THREADS']='1'
VERIFIER_START_SHA256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()

def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def files(): return sorted([ROOT/'AnvBandit.lean', *ROOT.joinpath('AnvBandit').rglob('*.lean')])
def digest():
    paths=files()+[ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'lake-manifest.json']
    return ''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(ROOT).as_posix()+'\n' for p in sorted(paths))
def command(args, log, append=False):
    with log.open('a' if append else 'w',encoding='utf-8') as out:
        def emit(line): out.write(line+'\n');out.flush(); print(line,flush=True)
        emit('UTC_START '+utc()); emit('CWD '+str(ROOT)); emit('COMMAND '+shlex.join(map(str,args)))
        proc=subprocess.Popen(list(map(str,args)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
        for line in proc.stdout: out.write(line);out.flush();print(line,end='',flush=True)
        code=proc.wait();emit('EXIT_CODE '+str(code));emit('UTC_END '+utc())
        if code: raise SystemExit(code)

# Default mode ALWAYS deletes the project build and rebuilds every source module.
# Resume is explicit verifier-script recovery, never an automatic shortcut.
resume = sys.argv[1:] == ['--resume-audit']
if sys.argv[1:] and not resume:
    raise SystemExit('Usage: verify_project.py [--resume-audit]')
source_files=files()
modules=[p.relative_to(ROOT).with_suffix('').as_posix().replace('/','.') for p in source_files]
build_dir=ROOT/'.lake/build'
buildlog=OUT/'CLEAN_BUILD_LOG.txt'
if resume:
    before=(OUT/'SOURCE_SHA256.txt').read_text(encoding='utf-8')
    if before != digest(): raise SystemExit('FAIL: sources/config changed since clean-build snapshot')
    expected='\n'.join(m+'\tPASS' for m in modules)+'\n'
    if (OUT/'BUILT_MODULES.txt').read_text(encoding='utf-8') != expected:
        raise SystemExit('FAIL: prior clean-build module coverage differs')
    prior=buildlog.read_text(encoding='utf-8')
    if 'Build completed successfully' not in prior or not re.search(r'EXIT_CODE 0\nUTC_END [^\n]+\n?$',prior):
        raise SystemExit('FAIL: no successful exhaustive clean-build log to resume')
    if not all((build_dir/'lib/lean'/pathlib.Path(*m.split('.'))).with_suffix('.olean').is_file() for m in modules):
        raise SystemExit('FAIL: a freshly built module artifact is absent')
    command(['lean','--version'],OUT/'AUDIT_RESUME_LOG.txt')
    command(['lake','--version'],OUT/'AUDIT_RESUME_LOG.txt',True)
    command([sys.executable,OUT/'check_dependencies.py',ROOT,ROOT/'.lake/packages'],OUT/'DEPENDENCY_REVISIONS_RESUME.txt')
else:
    # Freeze the input inventory before any build or audit.
    before=digest();(OUT/'SOURCE_SHA256.txt').write_text(before,encoding='utf-8')
    source_files=files(); modules=[p.relative_to(ROOT).with_suffix('').as_posix().replace('/','.') for p in source_files]
    (OUT/'TARGETS.txt').write_text('\n'.join(modules)+'\n',encoding='utf-8')
    buildlog=OUT/'CLEAN_BUILD_LOG.txt'
    command(['lean','--version'],buildlog)
    command(['lake','--version'],buildlog,True)
    command([sys.executable,OUT/'check_dependencies.py',ROOT,ROOT/'.lake/packages'],OUT/'DEPENDENCY_REVISIONS.txt')
    version=subprocess.check_output(['lean','--version'],text=True)
    if 'version 4.32.2,' not in version: raise SystemExit('FAIL: expected exact Lean 4.32.2')
    if (ROOT/'lean-toolchain').read_text(encoding='utf-8').strip()!='leanprover/lean4:v4.32.2': raise SystemExit('FAIL: toolchain pin changed')
    manifest=json.loads((ROOT/'lake-manifest.json').read_text(encoding='utf-8'))
    if next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')!='905b95818eb32af7874a58b427f50c1711a5e96c': raise SystemExit('FAIL: mathlib pin changed')
    # Only the project build directory is removed: pinned dependency caches are preserved.
    build_dir=ROOT/'.lake/build'
    if build_dir.is_symlink(): raise SystemExit('FAIL: project build directory may not be a symlink')
    if build_dir.exists(): shutil.rmtree(build_dir)
    with buildlog.open('a',encoding='utf-8') as out:
        out.write('PROJECT_BUILD_DIRECTORY_ABSENT_AFTER_CLEANUP '+str(build_dir)+'\n')
        out.write('PROJECT_SOURCE_MODULES '+str(len(modules))+'\n')
        out.write('DEPENDENCY_CACHE_POLICY pinned dependency caches may be reused; no project oleans reused; --no-cache prevents remote project cache fetch\n')
    # + disambiguates every module target, including all check modules and orphan sources.
    command(['lake','--no-cache','--no-ansi','build',*['+'+m for m in modules]],buildlog,True)
    missing=[m for m in modules if not (build_dir/'lib/lean'/pathlib.Path(*m.split('.'))).with_suffix('.olean').is_file()]
    if missing: raise SystemExit('FAIL: missing rebuilt oleans: '+repr(missing))
    (OUT/'BUILT_MODULES.txt').write_text('\n'.join(m+'\tPASS' for m in modules)+'\n',encoding='utf-8')
version=subprocess.check_output(['lean','--version'],text=True)
if 'version 4.32.2,' not in version: raise SystemExit('FAIL: expected exact Lean 4.32.2')
command(['lake','env',sys.executable,'-c','import os; print("LEAN_PATH="+os.environ.get("LEAN_PATH","")); print("LEAN_SRC_PATH="+os.environ.get("LEAN_SRC_PATH","")); print("LEAN_NUM_THREADS="+os.environ.get("LEAN_NUM_THREADS",""))'],OUT/'LAKE_ENVIRONMENT.txt')
command(['lake','env','lean','AnvBandit/Check.lean'],OUT/'CLEAN_CHECK_LOG.txt')

imports='\n'.join('import '+m for m in modules)+'\nimport Lean.Elab.Command\nimport Lean.Util.CollectAxioms\nimport Lean.Compiler.Old\nimport Lean.Meta.RecExt\n'
audit=imports+'''
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.header.modules
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  let mut moduleCount : Nat := 0
  let mut runtimeHelperCount : Nat := 0
  let mut used : Array Name := #[]
  for idx in [:modules.size] do
    let mod := modules[idx]!.module
    if mod.toString == "AnvBandit" || mod.toString.startsWith "AnvBandit." then
      moduleCount := moduleCount + 1
      let entries := env.header.moduleData[idx]!.constants.qsort (fun a b => Name.lt a.name b.name)
      logInfo m!"AUDIT_MODULE {mod} declarations={entries.size}"
      for info in entries do
        let name := info.name
        count := count + 1
        if info.isTheorem then theoremCount := theoremCount + 1
        if info.isAxiom then throwError "Project custom axiom: {name}"
        if info.isUnsafe then throwError "Project unsafe declaration: {name}"
        if info.isPartial then
          let some parent := Compiler.isUnsafeRecName? name
            | throwError "Non-generated project partial declaration: {name}"
          let some (.defnInfo parentInfo) := env.find? parent
            | throwError "Runtime companion lacks a kernel definition parent: {name}"
          if parentInfo.safety != .safe then throwError "Runtime companion parent is not safe: {name}"
          if parentInfo.levelParams != info.levelParams || parentInfo.type != info.type then
            throwError "Runtime companion type/levels differ from parent: {name}"
          let some helperModule := env.getModuleIdxFor? name
            | throwError "Runtime companion lacks module provenance: {name}"
          if env.getModuleIdxFor? parent != some helperModule then
            throwError "Runtime companion and parent have different modules: {name}"
          unless (← liftCoreM <| Meta.isRecursiveDefinition parent) do
            throwError "Runtime companion parent lacks recursive-definition tag: {name}"
          runtimeHelperCount := runtimeHelperCount + 1
          logInfo m!"AUDIT_COMPILER_RUNTIME_HELPER {name} parent={parent} safe_def=true recursive_tag=true type_levels_equal=true same_module=true"
        else
          let mut refs := info.type.getUsedConstants
          if let some value := info.value? (allowOpaque := true) then
            refs := refs ++ value.getUsedConstants
          for ref in refs do
            if let some refInfo := env.find? ref then
              if refInfo.isUnsafe || refInfo.isPartial then
                throwError "Safe kernel declaration {name} directly references unsafe/partial {ref}"
        let axioms ← collectAxioms name
        for ax in axioms do
          if !allowed.contains ax then throwError "Nonstandard axiom {ax} in {name}"
          if !used.contains ax then used := used.push ax
        logInfo m!"AUDIT_DECL {mod} :: {name} :: axioms={axioms.qsort Name.lt}"
  if count == 0 then throwError "No project declarations were checked"
  if moduleCount != EXPECTED_PROJECT_MODULES then throwError "Project module coverage mismatch: {moduleCount}"
  logInfo m!"ALL_PROJECT_AXIOMS_PASS modules={moduleCount} declarations={count} theorems={theoremCount} compiler_runtime_helpers={runtimeHelperCount} safe_kernel_references_checked=true allowed_used={used.qsort Name.lt}"
'''
audit=audit.replace('EXPECTED_PROJECT_MODULES',str(len(modules)))
(OUT/'AllAxioms.lean').write_text(audit,encoding='utf-8')
command(['lake','env','lean','verification/AllAxioms.lean'],OUT/'CLEAN_AXIOMS.txt')
# Keep exact endpoint and model signatures visible, with proof terms suppressed.
names='''AnvBandit.DecayModel
AnvBandit.ContactMatrix
AnvBandit.ContactMatrix.ofStochasticIrreducible
AnvBandit.Execution.Params
AnvBandit.Execution.LocalState
AnvBandit.Execution.State
AnvBandit.Execution.LocalState.choose
AnvBandit.Execution.run
AnvBandit.ExecutionUCB.extendedIndex
AnvBandit.ExecutionUCB.priorityChoice_spec
AnvBandit.ExecutionUCB.priorityChoice_eq_min_argmax
AnvBandit.ExecutionUCB.cooperative_choose_eq_min_argmax
AnvBandit.ExecutionUCB.baseline_choose_eq_min_argmax
AnvBandit.ExecutionLaw.rewardDistribution
AnvBandit.ExecutionLaw.contactDistribution
AnvBandit.ExecutionLaw.observedMeasure
AnvBandit.TrajectoryExpectation.teamRegret
AnvBandit.GlobalRegret.weightedLoss
AnvBandit.Main.actualCaps
AnvBandit.Main.actualEcost
AnvBandit.Main.canonicalContact
AnvBandit.Main.theorem_C_4
AnvBandit.Main.theorem_4_1
AnvBandit.Main.theorem_4_1_canonical
AnvBandit.ObservedRegret.original_theorem_4_1
AnvBandit.ObservedRegret.original_theorem_C_4
AnvBandit.ActualExplicitRegret.actual_explicit_canonical
AnvBandit.ActualExplicitRegret.actual_time_order
AnvBandit.ActualExplicitRegret.actual_Hxi_order
AnvBandit.ActualExplicitRegret.actual_fixed_h_log_order
AnvBandit.ActualExplicitRegret.actual_sublinear
AnvBandit.BaselineRealizedReward.original_realized_regret_bound
AnvBandit.BaselineComparison.cooperativeBound
AnvBandit.BaselineComparison.independentBound
AnvBandit.BaselineComparison.corollary_4_2'''.splitlines()
# Include all explicitly printed names from delivered check modules as well.
for p in source_files:
    names.extend(re.findall(r'^\s*#print\s+(?:axioms\s+)?(AnvBandit[\w.]+)',p.read_text(encoding='utf-8'),re.M))
names=list(dict.fromkeys(names))
(OUT/'Signatures.lean').write_text(imports+'\nset_option pp.proofs false\nset_option pp.universes true\n'+''.join('#print '+n+'\n' for n in names),encoding='utf-8')
command(['lake','env','lean','verification/Signatures.lean'],OUT/'CLEAN_SIGNATURES.txt')
# Supplemental lexical scan, never a replacement for elaboration and transitive axioms.
def remove_comments_strings(s):
    result=[];i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1;i+=2
            elif s.startswith('-/',i): depth-=1;i+=2
            else: result.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            if s[i]=='\\': result.extend('  ');i+=2
            elif s[i]=='"': string=False;result.append(' ');i+=1
            else: result.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i): depth=1;result.extend('  ');i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i);j=len(s) if j<0 else j;result.extend(' '*(j-i));i=j
        elif s[i]=='"': string=True;result.append(' ');i+=1
        else: result.append(s[i]);i+=1
    return ''.join(result)
pattern=re.compile(r'(?<![\w.])(?:sorry|admit|axiom|native_decide|unsafe|partial|partial_fixpoint|implemented_by|extern|reduceBool|trustLevel|debug\.skipKernelTC)(?![\w.])|_unsafe_rec')
findings=[]
for p in source_files:
    stripped=remove_comments_strings(p.read_text(encoding='utf-8'))
    for m in pattern.finditer(stripped): findings.append(f'{p.relative_to(ROOT)}:{stripped.count(chr(10),0,m.start())+1}: {m.group()}')
(OUT/'SOURCE_SCAN.txt').write_text(('\n'.join(findings) if findings else 'PASS: no forbidden tokens outside comments/strings')+'\nSupplemental scan only; see CLEAN_AXIOMS.txt for kernel declaration and transitive axiom audit.\n',encoding='utf-8')
if findings: raise SystemExit('FAIL: source scan requires review: '+repr(findings))
after=digest();(OUT/'SOURCE_SHA256_AFTER.txt').write_text(after,encoding='utf-8')
if before!=after: raise SystemExit('FAIL: project sources/config changed during verification')
command([sys.executable,OUT/'check_dependencies.py',ROOT,ROOT/'.lake/packages'],OUT/'DEPENDENCY_REVISIONS_AFTER.txt')
if hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()!=VERIFIER_START_SHA256:
    raise SystemExit('FAIL: verifier driver changed while running')
verifier_files=[OUT/n for n in ['verify_project.py','check_dependencies.py','verify.sh','verify.ps1','AllAxioms.lean','Signatures.lean']]
(OUT/'VERIFIER_SHA256.txt').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(ROOT).as_posix()+'\n' for p in verifier_files),encoding='utf-8')
audit_mode = 'explicit_resume_after_successful_clean_build' if resume else 'single_clean_invocation'
summary=f'FULL_CLEAN_VERIFICATION_PASS\nUTC_END {utc()}\nMODULES {len(modules)}\nLEAN 4.32.2\nMATHLIB 905b95818eb32af7874a58b427f50c1711a5e96c\nSOURCE_HASHES_UNCHANGED true\nAUDIT_MODE {audit_mode}\n'
(OUT/'RESULT.txt').write_text(summary,encoding='utf-8');print(summary,flush=True)
