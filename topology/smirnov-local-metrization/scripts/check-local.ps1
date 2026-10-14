param([string]$Module = 'Smirnov')
$ErrorActionPreference = 'Stop'
Push-Location (Split-Path -Parent $PSScriptRoot)
try { & lake build $Module; exit $LASTEXITCODE } finally { Pop-Location }
