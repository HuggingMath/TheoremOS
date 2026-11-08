#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
  printf 'Usage: %s /absolute/path/outside/the/proof-kit\n' "$0" >&2
  exit 2
fi

kit_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
if [[ $1 != /* ]]; then
  printf 'The tool directory must be an absolute path.\n' >&2
  exit 2
fi
tool_dir=$(realpath -m -- "$1")
cache_dir=$(realpath -m -- "$kit_dir/.lake")
case "$tool_dir/" in
  "$kit_dir/"*|"$cache_dir/"*)
    printf 'Install tools outside the proof kit and its writable cache.\n' >&2
    exit 2
    ;;
esac

if ! command -v elan >/dev/null 2>&1 && [[ -x ${ELAN_HOME:-$HOME/.elan}/bin/elan ]]; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi
for command_name in git go cargo cc elan realpath install sha256sum; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    printf 'Missing required command: %s\n' "$command_name" >&2
    exit 1
  fi
done
toolchain=$(tr -d '\r\n' < "$kit_dir/lean-toolchain")
elan toolchain install "$toolchain"
mkdir -p -- "$tool_dir/bin" "$tool_dir/src" "$tool_dir/cache"

checkout_tool() {
  local name=$1 url=$2 revision=$3 source_dir="$tool_dir/src/$1"
  if [[ ! -d $source_dir/.git ]]; then
    git clone --filter=blob:none --no-checkout "$url" "$source_dir"
  fi
  git -C "$source_dir" fetch --depth 1 origin "$revision"
  git -C "$source_dir" checkout --detach "$revision"
  [[ $(git -C "$source_dir" rev-parse HEAD) == "$revision" ]]
}

landrun_revision=5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
export GOPATH="$tool_dir/cache/gopath"
export GOCACHE="$tool_dir/cache/go-build"
export GOMODCACHE="$tool_dir/cache/go-modules"
GOBIN="$tool_dir/bin" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_revision"

exporter_revision=076e8e57707e813375e8f9da8bf989799ace9680
checkout_tool lean4export https://github.com/leanprover/lean4export.git "$exporter_revision"
cp -- "$kit_dir/lean-toolchain" "$tool_dir/src/lean4export/lean-toolchain"
(
  cd -- "$tool_dir/src/lean4export"
  elan run "$toolchain" lake build lean4export
)
install -m 755 -- "$tool_dir/src/lean4export/.lake/build/bin/lean4export" "$tool_dir/bin/lean4export"

comparator_revision=d03acab154d269c06e60e4de7e4cc85deebff94b
checkout_tool comparator https://github.com/leanprover/comparator.git "$comparator_revision"
cp -- "$kit_dir/lean-toolchain" "$tool_dir/src/comparator/lean-toolchain"
(
  cd -- "$tool_dir/src/comparator"
  elan run "$toolchain" lake build comparator
)
install -m 755 -- "$tool_dir/src/comparator/.lake/build/bin/comparator" "$tool_dir/bin/comparator"

nanoda_revision=68d5ca9db226849b41a6fff59d796ff19d0a8840
checkout_tool nanoda https://github.com/robsimmons/nanoda_lib.git "$nanoda_revision"
export CARGO_HOME="$tool_dir/cache/cargo"
export CARGO_TARGET_DIR="$tool_dir/build/nanoda"
cargo_options=()
if [[ -f $tool_dir/src/nanoda/Cargo.lock ]]; then
  cargo_options+=(--locked)
fi
cargo build --release "${cargo_options[@]}" --manifest-path "$tool_dir/src/nanoda/Cargo.toml"
install -m 755 -- "$CARGO_TARGET_DIR/release/nanoda_bin" "$tool_dir/bin/nanoda_bin"

for name in comparator landrun lean4export nanoda_bin; do
  ln -sfnT -- "$name" "$tool_dir/bin/theoremos-dimitrov-$name"
done

{
  printf 'export PATH=%q:"$PATH"\n' "$tool_dir/bin"
  printf 'export COMPARATOR_BIN=theoremos-dimitrov-comparator\n'
  printf 'export COMPARATOR_LANDRUN=theoremos-dimitrov-landrun\n'
  printf 'export COMPARATOR_LEAN4EXPORT=theoremos-dimitrov-lean4export\n'
  printf 'export COMPARATOR_NANODA=theoremos-dimitrov-nanoda_bin\n'
} > "$tool_dir/env.sh"

{
  printf 'tool\tsource_commit\tsha256\n'
  for entry in "landrun:$landrun_revision" "lean4export:$exporter_revision" "comparator:$comparator_revision" "nanoda_bin:$nanoda_revision"; do
    name=${entry%%:*}
    revision=${entry#*:}
    digest=$(sha256sum -- "$tool_dir/bin/$name")
    printf '%s\t%s\t%s\n' "$name" "$revision" "${digest%% *}"
  done
} > "$tool_dir/tool-versions.tsv"

printf 'Tools installed for %s. Enable them with:\nsource %q\n' "$toolchain" "$tool_dir/env.sh"
