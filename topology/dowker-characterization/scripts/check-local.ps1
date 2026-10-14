param([string]$Module = 'Defs')
$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [System.Text.UTF8Encoding]::new()
$dowkerCacheRoot = 'C:\Users\arfreita\Documents\Codex\2026-10-09\task-2\mathlib435'
$dowkerLeanExe = 'C:\Users\arfreita\.elan\toolchains\leanprover--lean4---v4.35.0-rc2\bin\lean.exe'
$dowkerProjectRoot = Split-Path -Parent $PSScriptRoot
$dowkerOutputRoot = Join-Path $dowkerProjectRoot '.lake\build\lib\lean'
New-Item -ItemType Directory -Force -Path $dowkerOutputRoot | Out-Null
$dowkerLeanPaths = @($dowkerOutputRoot, (Join-Path $dowkerCacheRoot '.lake\build\lib\lean'), 'C:\Users\arfreita\Documents\Codex\2026-10-11\task-2\Math-Formalization\topology\dowker-characterization\.lake\build\lib\lean')
Get-ChildItem -LiteralPath (Join-Path $dowkerCacheRoot '.lake\packages') -Directory | ForEach-Object {
  $dowkerLeanPaths += Join-Path $_.FullName '.lake\build\lib\lean'
}
$env:LEAN_PATH = $dowkerLeanPaths -join ';'
Push-Location $dowkerProjectRoot
try {
  & $dowkerLeanExe -j2 -M3072 -o (Join-Path $dowkerOutputRoot ($Module + '.olean')) ($Module + '.lean')
  exit $LASTEXITCODE
} finally { Pop-Location }

