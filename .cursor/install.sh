#!/usr/bin/env bash
# Idempotent Cloud Agent bootstrap for TheComfyOne/pequalnp-proofs.
# Puts tools on /usr/local/bin so login shells (bash -l) find them without rc files.
set -euo pipefail

NODE_VERSION="${NODE_VERSION:-22.23.4}"
KISSAT_VERSION="${KISSAT_VERSION:-4.0.4}"
CADICAL_VERSION="${CADICAL_VERSION:-3.1.0}"
ELAN_HOME="${ELAN_HOME:-${HOME}/.elan}"
CACHE_DIR="${PEQUALNP_CACHE_DIR:-${HOME}/.cache/pequalnp-env}"

log() { printf '[pequalnp-env] %s\n' "$*"; }
have() { command -v "$1" >/dev/null 2>&1; }
bin_major() {
  local v
  v="$("$1" -v 2>/dev/null | sed -n 's/^v\([0-9][0-9]*\).*/\1/p; s/^\([0-9][0-9]*\).*/\1/p' | head -n1)"
  printf '%s' "${v:-0}"
}

on_path() {
  export ELAN_HOME
  export PATH="/usr/local/bin:${ELAN_HOME}/bin:${PATH}"
  hash -r 2>/dev/null || true
}

link_elan() {
  mkdir -p "${ELAN_HOME}/bin"
  local f
  for f in elan lake lean leanc leanmake; do
    if [ -x "${ELAN_HOME}/bin/${f}" ]; then
      sudo ln -sfn "${ELAN_HOME}/bin/${f}" "/usr/local/bin/${f}"
    fi
  done
}

install_apt() {
  local pkgs=(ca-certificates curl git xz-utils unzip build-essential python3 python3-venv)
  local missing=() p
  for p in "${pkgs[@]}"; do
    dpkg -s "$p" >/dev/null 2>&1 || missing+=("$p")
  done
  if [ "${#missing[@]}" -gt 0 ]; then
    log "apt install: ${missing[*]}"
    sudo apt-get update -y
    sudo DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends "${missing[@]}"
  else
    log "apt packages already present"
  fi
}

install_node() {
  if [ -x /usr/local/bin/node ] && [ "$(bin_major /usr/local/bin/node)" -ge 20 ]; then
    log "Node.js $(/usr/local/bin/node -v) already in /usr/local/bin"
    return 0
  fi
  log "installing Node.js v${NODE_VERSION} into /usr/local"
  local tarball="node-v${NODE_VERSION}-linux-x64.tar.xz"
  mkdir -p "${CACHE_DIR}"
  if [ ! -f "${CACHE_DIR}/${tarball}" ]; then
    curl -fsSL "https://nodejs.org/dist/v${NODE_VERSION}/${tarball}" -o "${CACHE_DIR}/${tarball}"
  fi
  sudo tar -xJ -C /usr/local --strip-components=1 --no-same-owner -f "${CACHE_DIR}/${tarball}"
}

install_elan() {
  if [ ! -x "${ELAN_HOME}/bin/elan" ]; then
    log "installing elan"
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none --no-modify-path
  else
    log "elan already installed"
  fi
  link_elan
}

install_lean_toolchain() {
  local pin
  pin="$(tr -d '[:space:]' < lean/lean-toolchain)"
  [ -n "${pin}" ] || { log "missing lean/lean-toolchain"; exit 1; }
  log "ensuring Lean toolchain ${pin}"
  elan toolchain install "${pin}"
  elan default "${pin}"
  link_elan
}

fetch_mathlib_and_prebuild() {
  log "lake exe cache get (Mathlib oleans)"
  (cd lean && lake exe cache get)
  # Do not `lake build PEqualNP`: the library glob includes every Outside proof.
  log "prebuild PEqualNP.Defs (desk definitions root)"
  (cd lean && lake build PEqualNP.Defs)
  log "prebuild checklemma (tools/check-lean.mjs verifier)"
  (cd lean && lake build checklemma)
}

install_kissat() {
  if [ -x /usr/local/bin/kissat ]; then
    log "kissat already in /usr/local/bin"
    return 0
  fi
  if have kissat; then
    log "linking existing kissat $(command -v kissat) -> /usr/local/bin"
    sudo ln -sfn "$(command -v kissat)" /usr/local/bin/kissat
    return 0
  fi
  log "installing kissat ${KISSAT_VERSION}"
  mkdir -p "${CACHE_DIR}"
  local zip="kissat-${KISSAT_VERSION}-linux-amd64.zip"
  if [ ! -f "${CACHE_DIR}/${zip}" ]; then
    curl -fsSL "https://github.com/arminbiere/kissat/releases/download/rel-${KISSAT_VERSION}/${zip}" \
      -o "${CACHE_DIR}/${zip}"
  fi
  local tmp
  tmp="$(mktemp -d)"
  unzip -qo "${CACHE_DIR}/${zip}" -d "${tmp}"
  local bin
  bin="$(find "${tmp}" -type f \( -name kissat -o -name 'kissat-*linux*' \) | head -n1)"
  [ -n "${bin}" ] || { log "kissat binary missing from ${zip}"; exit 1; }
  chmod +x "${bin}"
  sudo install -m 755 "${bin}" /usr/local/bin/kissat
  rm -rf "${tmp}"
}

install_cadical() {
  if [ -x /usr/local/bin/cadical ]; then
    log "cadical already in /usr/local/bin"
    return 0
  fi
  if have cadical; then
    log "linking existing cadical $(command -v cadical) -> /usr/local/bin"
    sudo ln -sfn "$(command -v cadical)" /usr/local/bin/cadical
    return 0
  fi
  log "building cadical ${CADICAL_VERSION}"
  mkdir -p "${CACHE_DIR}"
  local src="${CACHE_DIR}/cadical-${CADICAL_VERSION}"
  if [ ! -x "${src}/build/cadical" ]; then
    local tar="rel-${CADICAL_VERSION}.tar.gz"
    if [ ! -f "${CACHE_DIR}/${tar}" ]; then
      curl -fsSL "https://github.com/arminbiere/cadical/archive/refs/tags/${tar}" \
        -o "${CACHE_DIR}/${tar}"
    fi
    rm -rf "${src}"
    mkdir -p "${src}"
    tar -xzf "${CACHE_DIR}/${tar}" -C "${src}" --strip-components=1
    (cd "${src}" && ./configure && make -j"$(nproc)")
  fi
  sudo install -m 755 "${src}/build/cadical" /usr/local/bin/cadical
}

verify_tools() {
  local missing=() t
  for t in elan lake lean node python3 gh kissat cadical; do
    if have "${t}"; then
      log "ok ${t}: $(command -v "${t}")"
    else
      missing+=("${t}")
    fi
  done
  if [ "${#missing[@]}" -gt 0 ]; then
    log "missing required tools: ${missing[*]}"
    exit 1
  fi
  node -e 'const m=parseInt(process.versions.node,10); if (m<20) { console.error("need Node.js 20+"); process.exit(1); }'
  python3 --version
  gh --version | head -n1
  lake --version | head -n1
  lean --version | head -n1
  kissat --version 2>/dev/null | head -n1 || kissat -v 2>/dev/null | head -n1 || true
  cadical --version 2>/dev/null | head -n1 || true
  log "install complete"
}

on_path
install_apt
install_node
on_path
install_elan
on_path
install_lean_toolchain
fetch_mathlib_and_prebuild
install_kissat
install_cadical
on_path
verify_tools
