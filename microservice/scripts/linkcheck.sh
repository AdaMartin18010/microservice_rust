#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

failed=0
while IFS= read -r -d '' file; do
  while IFS= read -r link; do
    # 仅检查相对路径型 Markdown 链接
    path="${link#*(}"
    path="${path%%)*}"
    if [[ "$path" == http* || "$path" == mailto:* || "$path" == \#* ]]; then
      continue
    fi
    if [[ -n "$path" && ! -e "$ROOT_DIR/docs/$path" ]]; then
      echo "Broken link: $file -> $path"
      failed=1
    fi
  done < <(grep -o "\[[^\]]*\](\([^)]\+\))" "$file" || true)
done < <(find docs -name "*.md" -print0)

exit $failed


