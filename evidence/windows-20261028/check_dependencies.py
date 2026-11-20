#!/usr/bin/env python3
"""Verify every locked dependency HEAD and tracked worktree against the frozen manifest."""
import hashlib, json, pathlib, subprocess, sys
project, packages = map(pathlib.Path, sys.argv[1:3])
manifest=json.loads((project/'lake-manifest.json').read_text(encoding='utf-8'))
print('DEPENDENCY_MANIFEST_SHA256', hashlib.sha256((project/'lake-manifest.json').read_bytes()).hexdigest())
for item in manifest['packages']:
    path=packages/item['name']
    def git(*args):
        return subprocess.check_output(['git','-C',str(path),*args], text=True).strip()
    actual=git('rev-parse','HEAD')
    print(f"{item['name']} expected={item['rev']} actual={actual}")
    if actual!=item['rev']:
        raise SystemExit(f"FAIL: revision mismatch for {item['name']}")
    status=git('status','--porcelain','--untracked-files=no')
    if status:
        raise SystemExit(f"FAIL: dirty tracked dependency {item['name']}\n{status}")
    hidden=[line for line in git('ls-files','-v').splitlines() if line and (line[0].islower() or line[0]=='S')]
    if hidden:
        raise SystemExit(f"FAIL: hidden tracked-file status flags in {item['name']}: {hidden[:5]}")
    diff=git('diff','--exit-code','HEAD','--')
    print(f"{item['name']} tracked files: clean; revision: locked")
print('DEPENDENCY_VERIFICATION_PASS')
