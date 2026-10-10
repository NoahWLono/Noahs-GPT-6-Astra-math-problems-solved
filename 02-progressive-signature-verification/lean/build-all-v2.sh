#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
while IFS= read -r module; do
  [[ -z "$module" ]] && continue
  echo "Checking $module"
  "$here/check.sh" "$module" > "$here/$module.log" 2>&1
done < "$here/modules-v2.txt"
echo 'All v2 listed modules checked successfully.'
