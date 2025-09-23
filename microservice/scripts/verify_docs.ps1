Param()
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
Set-Location $root

Write-Host "==> Running linkcheck"
powershell -NoProfile -ExecutionPolicy Bypass -File ./microservice/scripts/linkcheck.ps1

Write-Host "==> Running stylecheck"
powershell -NoProfile -ExecutionPolicy Bypass -File ./microservice/scripts/stylecheck.ps1

Write-Host "All doc checks passed."
exit 0


