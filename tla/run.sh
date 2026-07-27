#!/usr/bin/env bash
# Model-check the CPR snapshot specs and report each result against its
# expectation.
#
#   ./tla/run.sh
#
# Needs Java 11+ and curl (or wget). tla2tools.jar is downloaded on first run
# and cached next to this script. Set TLA_TOOLS to use a copy you already have,
# or use the Dockerfile here if you would rather not install Java.
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"

JAR="${TLA_TOOLS:-}"
if [[ -z "$JAR" && -f /opt/tla2tools.jar ]]; then
  JAR=/opt/tla2tools.jar
fi
if [[ -z "$JAR" ]]; then
  JAR="$HERE/.tla2tools.jar"
fi

if ! command -v java >/dev/null 2>&1; then
  echo "error: java not found. Install a JRE (11 or newer), or run the checks in Docker:" >&2
  echo "  docker build -f tla/Dockerfile -t bftree-tla tla && docker run --rm bftree-tla" >&2
  exit 1
fi

if [[ ! -f "$JAR" ]]; then
  URL="https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar"
  echo "Downloading tla2tools.jar to $JAR ..."
  if command -v curl >/dev/null 2>&1; then
    curl -fsSL "$URL" -o "$JAR.tmp" || { echo "error: download failed" >&2; exit 1; }
  elif command -v wget >/dev/null 2>&1; then
    wget -qO "$JAR.tmp" "$URL" || { echo "error: download failed" >&2; exit 1; }
  else
    echo "error: need curl or wget to fetch tla2tools.jar, or set TLA_TOOLS" >&2
    exit 1
  fi
  mv "$JAR.tmp" "$JAR"
fi

TLC=(java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC -workers auto -deadlock -cleanup)
failures=0

run() {
  local spec="$1" cfg="$2" expected_result="$3" description="$4"
  local output status
  output="$(mktemp)"
  echo ""
  echo "############################################################"
  echo "# $spec   (config: $cfg)"
  echo "# expected: $expected_result ($description)"
  echo "############################################################"
  if (cd "$HERE" && "${TLC[@]}" -config "$cfg" "$spec.tla") >"$output" 2>&1; then
    status=0
  else
    status=$?
  fi
  cat "$output"

  if [[ "$expected_result" == "HOLDS" ]]; then
    if [[ $status -eq 0 ]] && grep -q "Model checking completed. No error has been found." "$output"; then
      echo "# ---- PASS: HOLDS ----"
    else
      echo "# ---- FAIL: expected HOLDS; TLC exit code $status ----"
      failures=$((failures + 1))
    fi
  elif [[ $status -ne 0 ]] && grep -Eq "Error: Invariant .* is violated" "$output"; then
    echo "# ---- PASS: expected invariant violation observed ----"
  else
    echo "# ---- FAIL: expected invariant violation; TLC exit code $status ----"
    failures=$((failures + 1))
  fi

  rm -f "$output"
}

echo "========= x86-TSO memory model (validates X86TSO.tla) ========="
run SBLitmus SBLitmus_NoFence.cfg VIOLATED "the model permits StoreLoad, as x86 does"
run SBLitmus SBLitmus_Fence.cfg   HOLDS    "MFENCE closes it; nothing else was quietly closing it"

echo ""
echo "========= CPR snapshot phase handshake on x86-TSO ========="
run BfTreeCprHandshake BfTreeCprHandshake_None.cfg         VIOLATED "upstream Release/Acquire; the double-check reads a stale global_state"
run BfTreeCprHandshake BfTreeCprHandshake_SeqCstStores.cfg HOLDS    "SeqCst stores only -- closes it on x86, NOT in the Rust memory model"

echo ""
echo "========= CPR snapshot sweep freeze on x86-TSO ========="
run BfTreeCprSweep BfTreeCprSweep_None.cfg         VIOLATED "upstream Release/Acquire; sweep walks the tree under a live writer"
run BfTreeCprSweep BfTreeCprSweep_SeqCstStores.cfg HOLDS    "SeqCst stores only -- closes it on x86, NOT in the Rust memory model"

echo ""
if [[ $failures -ne 0 ]]; then
  echo "$failures spec result(s) did not match expectations."
  exit 1
fi

echo "All specs matched expectations."
