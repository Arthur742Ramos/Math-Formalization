param([string]$Module)
$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [System.Text.UTF8Encoding]::new()
$cacheRoot = 'C:\Users\arfreita\Documents\Codex\2026-10-09\task-2\mathlib435'
$leanExe = 'C:\Users\arfreita\.elan\toolchains\leanprover--lean4---v4.35.0-rc2\bin\lean.exe'
$projectRoot = Split-Path -Parent $PSScriptRoot
$outputRoot = Join-Path $projectRoot '.lake\build\lib\lean'
$relative = $Module.Replace('.', '\') + '.olean'
$target = Join-Path $outputRoot $relative
New-Item -ItemType Directory -Force -Path (Split-Path -Parent $target) | Out-Null
$leanPaths = @($outputRoot, (Join-Path $cacheRoot '.lake\build\lib\lean'))
Get-ChildItem -LiteralPath (Join-Path $cacheRoot '.lake\packages') -Directory | ForEach-Object {
  $leanPaths += Join-Path $_.FullName '.lake\build\lib\lean'
}
$env:LEAN_PATH = $leanPaths -join ';'
$source = Join-Path $cacheRoot ($Module.Replace('.', '\') + '.lean')
& $leanExe -j2 -M3072 --root=$cacheRoot -o $target $source
exit $LASTEXITCODE
