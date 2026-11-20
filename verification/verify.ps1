$ErrorActionPreference = "Stop"
Set-Location (Join-Path $PSScriptRoot "..")
$env:LEAN_NUM_THREADS = "1"
if (Get-Command py -ErrorAction SilentlyContinue) {
    & py -3 verification/verify_project.py
} else {
    & python verification/verify_project.py
}
exit $LASTEXITCODE
