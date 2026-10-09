param([string]$Module = 'MichaelBiquotient')
$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [System.Text.UTF8Encoding]::new()
$cacheRoot = 'C:\Users\arfreita\Documents\Codex\2026-10-09\task-2\mathlib435'
$leanExe = 'C:\Users\arfreita\.elan\toolchains\leanprover--lean4---v4.35.0-rc2\bin\lean.exe'
$projectRoot = Split-Path -Parent $PSScriptRoot
$outputRoot = Join-Path $projectRoot '.lake\build\lib\lean'
New-Item -ItemType Directory -Force -Path $outputRoot | Out-Null
$leanPaths = @($outputRoot, (Join-Path $cacheRoot '.lake\build\lib\lean'))
Get-ChildItem -LiteralPath (Join-Path $cacheRoot '.lake\packages') -Directory | ForEach-Object {
  $leanPaths += Join-Path $_.FullName '.lake\build\lib\lean'
}
$env:LEAN_PATH = $leanPaths -join ';'
Push-Location $projectRoot
try {
  & $leanExe -j2 -M3072 -o (Join-Path $outputRoot ($Module + '.olean')) ($Module + '.lean')
  exit $LASTEXITCODE
} finally { Pop-Location }
