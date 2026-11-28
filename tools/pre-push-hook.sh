#!/bin/sh
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
#
# Pre-push hook for tools/push_gate.py (docs/lessons.md, rule 18). Nothing installs it. To use it, copy it by hand to
# "$(git rev-parse --git-path hooks)/pre-push". Git runs a pre-push hook in the top of the working tree with the remote's
# name and URL as arguments and the ref updates on stdin; the gate refuses anything but one fast-forward of a branch
# whose new commit is HEAD of a clean tree, then runs the checks for exactly the pushed commits.
exec python3 -I tools/push_gate.py --pre-push "$@" --run
