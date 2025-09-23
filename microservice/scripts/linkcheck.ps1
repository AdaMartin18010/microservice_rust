Param()
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
Set-Location $root

$failed = $false
Get-ChildItem -Path "$root/docs" -Recurse -Filter *.md | ForEach-Object {
  $file = $_.FullName
  $content = Get-Content $file -Raw
  $matches = Select-String -InputObject $content -Pattern '\[[^\]]*\]\(([^)]+)\)' -AllMatches
  foreach ($m in $matches.Matches) {
    $path = $m.Groups[1].Value
    if ($path.StartsWith('http') -or $path.StartsWith('mailto:') -or $path.StartsWith('#')) { continue }
    $target = Join-Path (Join-Path $root 'docs') $path
    if (-not (Test-Path $target)) {
      Write-Host "Broken link: $file -> $path"
      $failed = $true
    }
  }
}

if ($failed) { exit 1 } else { exit 0 }


