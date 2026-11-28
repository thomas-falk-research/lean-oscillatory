/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Front.StationaryLeadingSharpCellsCore

/-!
# Batch SPL-N, part N7: the 40 cells and their kernel check (helper of agent C)

Route `docs/proof-SPLN.md`, section 2, **N7**. The 40 cells of the packet's certificate (second target,
`q = 360987/500000`, copied from `spl-cells.json`) as a list of pairs of rationals, and the Boolean checks
`splnC_check` (every cell passes `splnC_cellOK`, and the cells cover `[1/2, 4]` in order) and `splnC_lowOK`
(the lower point of N9), both evaluated by the kernel with `decide +kernel`.
-/

namespace OscInt.SPLNAux

/-- The target `q = 360987/500000`. -/
def splnC_q : ℚ := 360987 / 500000

/-- The 40 cells `[a, b]` covering `[1/2, 4]`. -/
def splnC_cells : List (ℚ × ℚ) :=
  [(1/2, 15/16), (15/16, 37/32), (37/32, 11/8), (11/8, 95/64),
    (95/64, 197/128), (197/128, 401/256), (401/256, 51/32), (51/32, 823/512),
    (823/512, 1653/1024), (1653/1024, 3313/2048), (3313/2048, 415/256), (415/256, 6647/4096),
    (6647/4096, 13301/8192), (13301/8192, 26609/16384), (26609/16384, 53225/32768), (53225/32768, 106457/65536),
    (106457/65536, 3327/2048), (3327/2048, 212935/131072), (212935/131072, 106471/65536), (106471/65536, 212949/131072),
    (212949/131072, 53239/32768), (53239/32768, 106485/65536), (106485/65536, 26623/16384), (26623/16384, 53253/32768),
    (53253/32768, 13315/8192), (13315/8192, 6661/4096), (6661/4096, 1667/1024), (1667/1024, 3341/2048),
    (3341/2048, 837/512), (837/512, 1681/1024), (1681/1024, 211/128), (211/128, 429/256),
    (429/256, 109/64), (109/64, 225/128), (225/128, 29/16), (29/16, 65/32),
    (65/32, 9/4), (9/4, 43/16), (43/16, 25/8), (25/8, 4)]

/-- All cells pass and they cover `[1/2, 4]`. -/
def splnC_check : Bool :=
  splnC_cells.all (splnC_cellOK splnC_q) && splnC_chain (1 / 2) splnC_cells 4

theorem splnC_check_true : splnC_check = true := by decide +kernel

theorem splnC_lowOK_true : splnC_lowOK = true := by decide +kernel

end OscInt.SPLNAux
