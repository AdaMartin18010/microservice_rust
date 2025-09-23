Param()
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
Set-Location $root

$replacements = @(
  @{ From='\bopentelemetry\b'; To='OpenTelemetry' },
  @{ From='\bprometheus\b'; To='Prometheus' },
  @{ From='\bjaeger\b'; To='Jaeger' },
  @{ From='\bkubernetes\b'; To='Kubernetes' },
  @{ From='\bgrpc\b'; To='gRPC' },
  @{ From='\bhttp\b'; To='HTTP' }
)

Get-ChildItem -Path "$root/docs" -Recurse -Filter *.md | ForEach-Object {
  $file = $_.FullName
  $content = Get-Content $file -Raw
  $original = $content
  foreach ($r in $replacements) {
    $content = [regex]::Replace($content, $r.From, $r.To)
  }
  if ($content -ne $original) {
    Set-Content -Path $file -Value $content -NoNewline
    Write-Host "Updated: $file"
  }
}

exit 0


