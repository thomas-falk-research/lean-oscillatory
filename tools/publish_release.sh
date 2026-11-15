#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0

# Publish a release that release-candidate.yml prepared, checking everything before anything becomes public
# (a published release is archived by Zenodo with a permanent DOI, so the checks of post-release.yml come too late
# to stop a mistake). Run by the owner from a clone of the repository checked out at the release commit, with `gh`
# logged in:
#   tools/publish_release.sh vX.Y.Z <commit> <release-candidate run id> [--dry-run]
#   tools/publish_release.sh --body vX.Y.Z <commit> <run id> <owner/repo>   # the release body (release-candidate.yml)
#   tools/publish_release.sh --self-test     # the offline checks against planted defects (no network)
# The release-candidate run summary prints the exact commands. Before anything is created it checks that:
# - the run is a successful release-candidate dispatch on main for exactly <commit>, and <commit> is on origin/main;
# - the run's artifact has exactly the three assets, they match SHA256SUMS, and they equal the files of <commit>;
# - the release body is byte for byte the body that --body builds from <commit>'s release notes;
# - each asset's attestation was signed by release-candidate.yml, from refs/heads/main, for <commit>;
# - no release vX.Y.Z exists (not even a draft), and a tag vX.Y.Z, local or on origin, is annotated and points at
#   <commit> if it exists (a resumed run).
# --dry-run stops there. Otherwise it creates and pushes the annotated tag if needed, checks that origin's tag points
# at <commit>, creates the release as a draft with the checked files, checks that the draft has exactly the three
# assets, and only then publishes it.
set -euo pipefail

ASSETS=(SHA256SUMS oscint_check.py statements.json)

die() { echo "publish: STOP: $*" >&2; exit 1; }

# body TAG COMMIT RUN REPO: the release body, from docs/release-notes/TAG.md at COMMIT: two lines naming the commit,
# the run and the attestation check, then the notes from the "A minor/patch/major release" paragraph up to, not
# including, "## Publishing"
body() {
  local tag=$1 sha=$2 run=$3 repo=$4 notes part
  notes=$(git show "$sha:docs/release-notes/$tag.md") || die "no docs/release-notes/$tag.md at $sha"
  grep -q '^## Publishing' <<<"$notes" || die "docs/release-notes/$tag.md has no '## Publishing' section"
  part=$(awk '/^## Publishing/ { exit } /^A (minor|patch|major) release/ { on = 1 } on' <<<"$notes")
  [ -n "$part" ] || die "docs/release-notes/$tag.md has no paragraph starting 'A minor/patch/major release'"
  grep -q '^## Statement changes' <<<"$part" || die "the release body would have no '## Statement changes' section"
  # shellcheck disable=SC2016  # the backticks are Markdown, not command substitution
  printf 'Release commit: `%s` — checked by release-candidate run %s (full replay and CI on this commit).\n' "$sha" "$run"
  # shellcheck disable=SC2016
  printf 'Assets: `SHA256SUMS`; provenance: `gh attestation verify <asset> --repo %s --signer-workflow %s/.github/workflows/release-candidate.yml --source-ref refs/heads/main --source-digest %s`.\n\n' \
    "$repo" "$repo" "$sha"
  printf '%s\n' "$part"
}

# check_assets DIR TAG COMMIT RUN REPO: DIR is the downloaded artifact (dist/ and body/); COMMIT is in this clone
check_assets() {
  local dir=$1 tag=$2 sha=$3 run=$4 repo=$5 got want expect
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
  expect=$(mktemp); body "$tag" "$sha" "$run" "$repo" > "$expect"
  cmp -s "$expect" "$dir/body/notes.md" || { rm -f "$expect"; die "the release body is not the one built from $sha's notes"; }
  rm -f "$expect"
}

# tag_on_origin TAG: the commit origin's annotated tag TAG points at (empty if there is no such tag); stops on a
# lightweight tag, whose ls-remote has no peeled line
tag_on_origin() {
  local lines direct peeled
  lines=$(git ls-remote origin "refs/tags/$1" "refs/tags/$1^{}")
  direct=$(awk -v r="refs/tags/$1" '$2 == r { print $1 }' <<<"$lines")
  peeled=$(awk -v r="refs/tags/$1^{}" '$2 == r { print $1 }' <<<"$lines")
  if [ -n "$direct" ] && [ -z "$peeled" ]; then die "origin's tag $1 is lightweight; a release tag must be annotated"; fi
  printf '%s' "$peeled"
}

publish() {
  local tag=$1 sha=$2 run=$3 dry=${4:-} repo dir info remote out f
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
  check_assets "$dir" "$tag" "$sha" "$run" "$repo"
  for f in "${ASSETS[@]}"; do
    gh attestation verify "$dir/dist/$f" --repo "$repo" \
      --signer-workflow "$repo/.github/workflows/release-candidate.yml" \
      --source-ref refs/heads/main --source-digest "$sha" >/dev/null \
      || die "the attestation of $f is not release-candidate.yml's on main for $sha"
  done
  echo "publish: ok: assets, SHA256SUMS, release body and attestations"

  if out=$(gh release view "$tag" --repo "$repo" --json isDraft -q .isDraft 2>&1); then
    die "release $tag already exists (draft: $out); if it is a draft left by an interrupted run, check and delete it"
  elif ! grep -qi 'release not found' <<<"$out"; then
    die "cannot tell whether release $tag exists: $out"
  fi
  if git rev-parse -q --verify "refs/tags/$tag" >/dev/null; then
    [ "$(git cat-file -t "refs/tags/$tag")" = tag ] || die "the local tag $tag is lightweight; delete it (git tag -d $tag)"
    [ "$(git rev-parse "refs/tags/$tag^{commit}")" = "$sha" ] || die "the local tag $tag points elsewhere; delete it"
  fi
  remote=$(tag_on_origin "$tag")
  [ -z "$remote" ] || [ "$remote" = "$sha" ] || die "tag $tag already exists on origin at $remote, not $sha"
  if [ -n "$dry" ]; then echo "publish: dry run: every check passed; nothing was tagged or published"; return 0; fi

  if [ -z "$remote" ]; then
    git rev-parse -q --verify "refs/tags/$tag" >/dev/null || git tag -a "$tag" "$sha" -m "OscInt $tag"
    git push origin "refs/tags/$tag"
  fi
  [ "$(tag_on_origin "$tag")" = "$sha" ] || die "origin's tag $tag does not point at $sha"

  gh release create "$tag" --repo "$repo" --draft --verify-tag --title "OscInt $tag" --notes-file "$dir/body/notes.md" \
    "$dir/dist/statements.json" "$dir/dist/oscint_check.py" "$dir/dist/SHA256SUMS"
  [ "$(gh release view "$tag" --repo "$repo" --json assets -q '[.assets[].name] | sort | join(" ")')" \
    = "${ASSETS[*]}" ] || die "the draft release $tag does not have exactly the assets ${ASSETS[*]}; it stays a draft"
  gh release edit "$tag" --repo "$repo" --draft=false
  [ "$(gh release view "$tag" --repo "$repo" --json isDraft -q .isDraft)" = false ] || die "release $tag is still a draft"
  echo "publish: $tag published; post-release.yml now runs its checks, the consumer build and the pins pull request"
}

self_test() {
  local t rc=0 sha tag=v9.9.9 run=123 repo=o/r
  t=$(mktemp -d); trap 'rm -rf "$t"' RETURN
  git -C "$t" init -q repo
  mkdir -p "$t/repo/stamps" "$t/repo/tools" "$t/repo/docs/release-notes"
  echo '{"statements": []}' > "$t/repo/stamps/statements.json"; echo 'print("check")' > "$t/repo/tools/oscint_check.py"
  printf '# notes\n\nStatus: prepared.\n\nA minor release. Text.\n\n## Statement changes\n\nNone.\n\n## Publishing\n\nSteps.\n' \
    > "$t/repo/docs/release-notes/$tag.md"
  printf '# notes\n\nA minor release. Text.\n\n## Statement changes\n\nNone.\n' > "$t/repo/docs/release-notes/v9.9.8.md"
  printf '# notes\n\nA minor release. Text.\n\n## Evidence\n\n## Publishing\n' > "$t/repo/docs/release-notes/v9.9.7.md"
  git -C "$t/repo" add -A
  git -C "$t/repo" -c user.name=t -c user.email=t@t commit -q -m t
  sha=$(git -C "$t/repo" rev-parse HEAD)
  mk() {
    rm -rf "$t/a"; mkdir -p "$t/a/dist" "$t/a/body"
    cp "$t/repo/stamps/statements.json" "$t/repo/tools/oscint_check.py" "$t/a/dist/"
    (cd "$t/a/dist" && sha256sum statements.json oscint_check.py > SHA256SUMS)
    (cd "$t/repo" && body "$tag" "$sha" "$run" "$repo") > "$t/a/body/notes.md"
  }
  want() {  # name, expected exit status
    local got; (cd "$t/repo" && check_assets "$t/a" "$tag" "$sha" "$run" "$repo") >/dev/null 2>&1 && got=0 || got=1
    if [ "$got" -ne "$2" ]; then echo "publish_release self-test: FAIL: $1 (exit $got, want $2)"; rc=1; fi
  }
  wantbody() {  # name, notes tag, expected exit status
    local got; (cd "$t/repo" && body "$2" "$sha" "$run" "$repo") >/dev/null 2>&1 && got=0 || got=1
    if [ "$got" -ne "$3" ]; then echo "publish_release self-test: FAIL: $1 (exit $got, want $3)"; rc=1; fi
  }
  mk; want "clean artifact" 0
  mk; echo x >> "$t/a/dist/statements.json"; want "asset differs from SHA256SUMS" 1
  mk; echo x >> "$t/a/dist/statements.json"; (cd "$t/a/dist" && sha256sum statements.json oscint_check.py > SHA256SUMS)
  want "asset differs from the commit" 1
  mk; touch "$t/a/dist/extra.txt"; want "extra asset" 1
  mk; rm "$t/a/dist/oscint_check.py"; want "missing asset" 1
  mk; sed -i '/oscint_check.py/d' "$t/a/dist/SHA256SUMS"; want "SHA256SUMS lists one file" 1
  mk; sed -i 's/None\./Nothing./' "$t/a/body/notes.md"; want "body edited" 1
  mk; sed -i "s/run $run/run 124/" "$t/a/body/notes.md"; want "body names another run" 1
  mk; rm "$t/a/body/notes.md"; want "no body" 1
  wantbody "notes without '## Publishing'" v9.9.8 1
  wantbody "notes without statement changes" v9.9.7 1
  wantbody "no notes for the tag" v9.9.6 1
  (cd "$t/repo" && body "$tag" "$sha" "$run" "$repo") | grep -q '^Status' \
    && { echo "publish_release self-test: FAIL: the status line reached the body"; rc=1; }
  [ "$rc" -eq 0 ] && echo "publish_release self-test: PASS (12 planted defects detected, clean artifact accepted, status line excluded)"
  return "$rc"
}

case "${1:-}" in
  --self-test) self_test ;;
  --body) shift; [ $# -eq 4 ] || die "usage: tools/publish_release.sh --body vX.Y.Z <commit> <run id> <owner/repo>"
          body "$@" ;;
  ""|-h|--help) sed -n '2,23p' "$0"; exit 2 ;;
  *) if [ $# -lt 3 ] || [ $# -gt 4 ]; then die "usage: tools/publish_release.sh vX.Y.Z <commit> <run id> [--dry-run]"; fi
     publish "$@" ;;
esac
