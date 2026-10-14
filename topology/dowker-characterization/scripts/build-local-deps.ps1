param([string[]]$Modules = @('Mathlib.Topology.ShrinkingLemma', 'Mathlib.Topology.PartitionOfUnity'))
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
function Build-DowkerDependency([string]$dowkerModule) {
  $dowkerRelative = $dowkerModule.Replace('.', '\')
  foreach ($dowkerPath in $dowkerLeanPaths) {
    if (Test-Path -LiteralPath (Join-Path $dowkerPath ($dowkerRelative + '.olean'))) { return }
  }
  if (-not $dowkerModule.StartsWith('Mathlib.')) { throw "Missing non-Mathlib dependency $dowkerModule" }
  $dowkerSource = Join-Path $dowkerCacheRoot ($dowkerRelative + '.lean')
  $dowkerSourceText = Get-Content -LiteralPath $dowkerSource -Encoding utf8 -Raw
  foreach ($dowkerImport in [regex]::Matches($dowkerSourceText, '(?m)^(?:public |private )?import ([A-Za-z0-9_.]+)')) {
    Build-DowkerDependency $dowkerImport.Groups[1].Value
  }
  $dowkerOutput = Join-Path $dowkerOutputRoot ($dowkerRelative + '.olean')
  New-Item -ItemType Directory -Force -Path (Split-Path -Parent $dowkerOutput) | Out-Null
  Write-Output "Compiling pinned dependency $dowkerModule"
  & $dowkerLeanExe -j2 -M3072 -R $dowkerCacheRoot -o $dowkerOutput $dowkerSource
  if ($LASTEXITCODE -ne 0) { throw "Compilation failed: $dowkerModule" }
}
foreach ($dowkerRequestedModule in $Modules) { Build-DowkerDependency $dowkerRequestedModule }

