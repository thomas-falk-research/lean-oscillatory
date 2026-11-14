#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0

# Publish a release that release-candidate.yml prepared, checking everything before anything becomes public
# (a published release is archived by Zenodo with a permanent DOI, so the checks of post-release.yml come too late
# to stop a mistake). Run by the owner from a clone of the repository, with `gh` logged in:
#   tools/publish_release.sh vX.Y.Z <commit> <release-candidate run id> [--dry-run]
#   tools/publish_release.sh --self-test     # the offline asset checks against planted defects (no network)
# The release-candidate run summary prints the exact command. Before the tag is created it checks that:
# - the run is a successful release-candidate run on main for exactly <commit>;
# - its artifact has exactly the three assets, they match SHA256SUMS, and they equal the files of <commit>;
# - the release body names <commit> and contains the notes' statement changes;
# - each asset's attestation was signed by release-candidate.yml, from refs/heads/main, for <commit>;
# - <commit> is on origin/main, and no release vX.Y.Z exists; a tag vX.Y.Z may exist only if it already points at
#   <commit> (a resumed run).
# Then it creates and pushes the annotated tag, checks that the remote tag points at <commit>, creates the release
# with the checked files, and checks that the published assets are exactly the three. --dry-run stops before the tag.
set -euo pipefail

ASSETS=(SHA256SUMS oscint_check.py statements.json)

die() { echo "publish: STOP: $*" >&2; exit 1; }

# check_assets DIR COMMIT: DIR is the downloaded artifact (dist/ and body/); COMMIT is in the current repository
check_assets() {
  local dir=$1 sha=$2 got want
  if [ ! -d "$dir/dist" ] || [ ! -f "$dir/body/notes.md" ]; then die "$dir has no dist/ or body/notes.md"; fi
  got=$(cd "$dir/dist" && find . -mindepth 1 -printf '%P\n' | LC_ALL=C sort | tr '\n' ' ')
  want="$(printf '%s\n' "${ASSETS[@]}" | LC_ALL=C sort | tr '\n' ' ')"
  [ "$got" = "$want" ] || die "the assets are [$got], not exactly [$want]"
  [ "$(awk '{print $2}' "$dir/dist/SHA256SUMS" | LC_ALL=C sort | tr '\n' ' ')" = "oscint_check.py statements.json " ] \
    || die "SHA256SUMS does not list exactly oscint_check.py and statements.json"
  (cd "$dir/dist" && sha256sum --strict --quiet -c SHA256SUMS) || die "an asset does not match SHA256SUMS"
  git show "$sha:stamps/statements.json" | cmp -s - "$dir/dist/statements.json" \
    || die "statements.json is not stamps/statements.json of $sha"
  git show "$sha:tools/oscint_check.py" | cmp -s - "$dir/dist/oscint_check.py" \
    || die "oscint_check.py is not tools/oscint_check.py of $sha"
  grep -qF "$sha" "$dir/body/notes.md" || die "the release body does not name $sha"
  grep -q '^## Statement changes' "$dir/body/notes.md" || die "the release body has no '## Statement changes' section"
}

publish() {
  local tag=$1 sha=$2 run=$3 dry=${4:-} repo dir info remote f
  echo "$tag" | grep -qxE 'v[0-9]+\.[0-9]+\.[0-9]+' || die "'$tag' is not vX.Y.Z"
  echo "$sha" | grep -qxE '[0-9a-f]{40}' || die "'$sha' is not a full commit hash"
  echo "$run" | grep -qxE '[0-9]+' || die "'$run' is not a run id"
  [ -z "$dry" ] || [ "$dry" = --dry-run ] || die "unknown option '$dry'"
  repo=$(gh repo view --json nameWithOwner -q .nameWithOwner)
  echo "publish: $tag of $repo at $sha from release-candidate run $run${dry:+ (dry run)}"

  git fetch -q origin main --tags
  git cat-file -e "$sha^{commit}" || die "$sha is not in this clone after fetching origin"
  git merge-base --is-ancestor "$sha" origin/main || die "$sha is not on origin/main"

  info=$(gh run view "$run" --repo "$repo" --json workflowName,headBranch,headSha,event,status,conclusion \
           -q '[.workflowName, .headBranch, .headSha, .event, .status, .conclusion] | join(" ")')
  [ "$info" = "release-candidate main $sha workflow_dispatch completed success" ] \
    || die "run $run is '$info', not a successful release-candidate dispatch on main for $sha"

  dir=$(mktemp -d "${TMPDIR:-/tmp}/release-$tag.XXXXXX")   # fresh on every run, so the assets come from run $run
  gh run download "$run" --repo "$repo" -n "release-$tag" -D "$dir"
  echo "publish: assets of run $run in $dir"
  check_assets "$dir" "$sha"
  for f in "${ASSETS[@]}"; do
    gh attestation verify "$dir/dist/$f" --repo "$repo" \
      --signer-workflow "$repo/.github/workflows/release-candidate.yml" \
      --source-ref refs/heads/main --source-digest "$sha" >/dev/null \
      || die "the attestation of $f is not release-candidate.yml's on main for $sha"
  done
  echo "publish: ok: assets, SHA256SUMS, release body and attestations"

  if gh release view "$tag" --repo "$repo" >/dev/null 2>&1; then die "release $tag already exists"; fi
  remote=$(git ls-remote origin "refs/tags/$tag^{}" | cut -f1)
  [ -z "$remote" ] || [ "$remote" = "$sha" ] || die "tag $tag already exists on origin at $remote, not $sha"
  if [ -n "$dry" ]; then echo "publish: dry run: every check passed; nothing was tagged or published"; return 0; fi

  if [ -z "$remote" ]; then
    if git rev-parse -q --verify "refs/tags/$tag" >/dev/null; then
      [ "$(git rev-parse "$tag^{commit}")" = "$sha" ] || die "a local tag $tag points elsewhere; delete it first"
    else
      git tag -a "$tag" "$sha" -m "OscInt $tag"
    fi
    git push origin "refs/tags/$tag"
  fi
  [ "$(git ls-remote origin "refs/tags/$tag^{}" | cut -f1)" = "$sha" ] || die "origin's tag $tag does not point at $sha"

  gh release create "$tag" --repo "$repo" --verify-tag --title "OscInt $tag" --notes-file "$dir/body/notes.md" \
    "$dir/dist/statements.json" "$dir/dist/oscint_check.py" "$dir/dist/SHA256SUMS"
  [ "$(gh release view "$tag" --repo "$repo" --json assets -q '[.assets[].name] | sort | join(" ")')" \
    = "${ASSETS[*]}" ] || die "the published release does not have exactly the assets ${ASSETS[*]}"
  echo "publish: $tag published; post-release.yml now runs its checks, the consumer build and the pins pull request"
}

self_test() {
  local t rc=0 sha
  t=$(mktemp -d); trap 'rm -rf "$t"' RETURN
  git -C "$t" init -q repo
  mkdir -p "$t/repo/stamps" "$t/repo/tools"
  echo '{"statements": []}' > "$t/repo/stamps/statements.json"; echo 'print("check")' > "$t/repo/tools/oscint_check.py"
  git -C "$t/repo" add -A
  git -C "$t/repo" -c user.name=t -c user.email=t@t commit -q -m t
  sha=$(git -C "$t/repo" rev-parse HEAD)
  mk() {
    rm -rf "$t/a"; mkdir -p "$t/a/dist" "$t/a/body"
    cp "$t/repo/stamps/statements.json" "$t/repo/tools/oscint_check.py" "$t/a/dist/"
    (cd "$t/a/dist" && sha256sum statements.json oscint_check.py > SHA256SUMS)
    # shellcheck disable=SC2016  # the backticks are Markdown, not command substitution
    printf 'Release commit: `%s`\n\n## Statement changes\n\nNone.\n' "$sha" > "$t/a/body/notes.md"
  }
  want() {  # name, expected exit status
    local got; (cd "$t/repo" && check_assets "$t/a" "$sha") >/dev/null 2>&1 && got=0 || got=1
    if [ "$got" -ne "$2" ]; then echo "publish_release self-test: FAIL: $1 (exit $got, want $2)"; rc=1; fi
  }
  mk; want "clean artifact" 0
  mk; echo x >> "$t/a/dist/statements.json"; want "asset differs from SHA256SUMS" 1
  mk; echo x >> "$t/a/dist/statements.json"; (cd "$t/a/dist" && sha256sum statements.json oscint_check.py > SHA256SUMS)
  want "asset differs from the commit" 1
  mk; touch "$t/a/dist/extra.txt"; want "extra asset" 1
  mk; rm "$t/a/dist/oscint_check.py"; want "missing asset" 1
  mk; sed -i '/oscint_check.py/d' "$t/a/dist/SHA256SUMS"; want "SHA256SUMS lists one file" 1
  mk; sed -i "s/$sha/0000/" "$t/a/body/notes.md"; want "body does not name the commit" 1
  mk; sed -i '/^## Statement changes/d' "$t/a/body/notes.md"; want "body without statement changes" 1
  mk; rm "$t/a/body/notes.md"; want "no body" 1
  [ "$rc" -eq 0 ] && echo "publish_release self-test: PASS (8 planted defects detected, clean artifact accepted)"
  return "$rc"
}

case "${1:-}" in
  --self-test) self_test ;;
  ""|-h|--help) sed -n '2,20p' "$0"; exit 2 ;;
  *) if [ $# -lt 3 ] || [ $# -gt 4 ]; then die "usage: tools/publish_release.sh vX.Y.Z <commit> <run id> [--dry-run]"; fi
     publish "$@" ;;
esac
