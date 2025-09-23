Param()
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
Set-Location $root

$failed = $false
$rules = @(
  @{ Pattern = '\bopentelemetry\b'; Message = 'Use OpenTelemetry (case)'; },
  @{ Pattern = '\bprometheus\b'; Message = 'Use Prometheus (case)'; },
  @{ Pattern = '\bjaeger\b'; Message = 'Use Jaeger (case)'; },
  @{ Pattern = '\bkubernetes\b'; Message = 'Use Kubernetes (case)'; },
  @{ Pattern = '\bgrpc\b'; Message = 'Use gRPC (case)'; },
  @{ Pattern = '\bhttp\b'; Message = 'Use HTTP (case)'; }
)

Get-ChildItem -Path "$root/docs" -Recurse -Filter *.md | ForEach-Object {
  $file = $_.FullName
  $content = Get-Content $file -Raw
  # 预处理：忽略代码块、行内代码与 URL 链接
  $sanitized = $content
  # 去除三引号代码块
  $sanitized = [regex]::Replace($sanitized, '```[\s\S]*?```', '', 'IgnoreCase')
  # 去除行内代码
  $sanitized = [regex]::Replace($sanitized, '`[^`]*`', '', 'IgnoreCase')
  # 去除 URL
  $sanitized = [regex]::Replace($sanitized, 'https?://\S+', '', 'IgnoreCase')
  # 去除 Markdown 链接中的目标部分
  $sanitized = [regex]::Replace($sanitized, '\[[^\]]*\]\(([^)]+)\)', '$1', 'IgnoreCase')
  foreach ($r in $rules) {
    $m = Select-String -InputObject $sanitized -Pattern $r.Pattern -AllMatches -CaseSensitive
    if ($m.Matches.Count -gt 0) {
      Write-Host "Style warning: $file -> $($r.Message) ($($m.Matches.Count))"
      $failed = $true
    }
  }
}

if ($failed) { exit 2 } else { exit 0 }


