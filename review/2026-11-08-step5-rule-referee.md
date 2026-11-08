bbafeeb84f73ebdfa5e326c04138a2924a25ab86 — referee report, 2026-11-08

# Adversarial referee: amended CONTRIBUTING step 5 (test-layer exception), memo `docs/decisions/2026-11-08-step5-memo.md`

Commit reviewed: bbafeeb (HEAD at the time of review, `git log -1` confirmed; working tree clean). I modified nothing in the
repository and ran no Lean or lake command. Everything below comes from reading files and from git (`git log`, `git show`,
`git diff`, `git grep`, `git ls-tree`). Where a claim needs a compiler run that I did not do, I label it CONJECTURED.

Read: the memo; `CONTRIBUTING.md`; `docs/lessons.md` 11, 16, 17, 23, 24, 29, 33 (and 25, 28, 35 for context);
`review/2026-11-08-API3-{pre-proof-A,pre-proof-B,pre-proof-answers,adversarial,answers}.md`; the post-proof prompt and the
adversarial prompt (`review/prompts/API3-post-proof.md`, `API3-adversarial.md`); `git show 7bb4579:OscInt/Front/FamilySanity.lean`;
`OscInt/Front/FamilySanity2.lean`; `docs/replay/2026-11-08-API3-sanity-plants.txt`; `docs/replay/plants/2026-11-08-API3/*`;
`stamps/20261108T010546Z-7bb457958327/manifest.txt`; `docs/STATUS.md` rows 33–42; `git log 6acef2a..bbafeeb`.

## Verdict

**Rule text §3(i): ADOPTABLE-WITH-CHANGES.** The changes are listed as exact text in §F. Without them the exception has two
structural holes: (1) the checks that guard it run after the proofs, when the fallback (re-freeze) is the one the memo itself
calls worthless; (2) clauses (b) and (c) can be met by evidence that tests the proof script, not the features the finding
names.

**Waiver sentence: NOT ACCURATE as worded.** It must be replaced (text in §F.2) before the owner ratifies it. It claims (a) and
(f) were met when they were not, or only in part. It says (c) was met "all after", but at bbafeeb planted controls exist for 3
of 10 statements. It does not mention (e) at all.

**Memo §2: one false fact.** The "second part of the plant record" does not exist. The same false claim is in
`review/2026-11-08-API3-answers.md:29`.

## Findings (summary)

| # | Label | Where | One line |
|---|---|---|---|
| 1 | BLOCKER | memo:57-59 (waiver) | Overstates the evidence. (a) and (f) not met as worded; (c) is 3/10, not "all"; (e) not mentioned |
| 2 | MAJOR | memo:25; `review/2026-11-08-API3-answers.md:29` | "M2 plants rejected (second part of the plant record)": no second part exists; the M2 outcomes are recorded only in a commit message |
| 3 | MAJOR | §3(i) (f) and the last sentence | Conditions are verified only after the proofs, so the fallback "a new statement" is toothless when it fires; (f) itself has no fallback |
| 4 | MAJOR | §3(i) (b) | Allows a sanity theorem that passes hypotheses through as its own assumptions (the lessons-11 restatement again) and does not require it to state the constant's conclusion |
| 5 | MAJOR | §3(i) (c) | One plant per statement, chosen by the lead, and any elaboration error counts. Brittleness is enough (adversarial m4); nothing ties the plant to the features the finding names |
| 6 | MAJOR | §3(i) (d), memo §4 | Plants the referee names that weaken a hypothesis are only listed and left to the referees who already passed the statements. Def-bundling with bite instances covers this class by machine; the exception should not apply when the finding names such plants |
| 7 | MAJOR | §3(i) (a) | Allows FAITHFUL-STRONGER/WEAKER without saying against what; against `docs/statements.md` either verdict means the statement does not say what the docs say |
| 8 | MAJOR | memo §4 | "Strictly stronger than def-bundling for the plants it covers" and "(ii) … without making any claim stronger" overstate. The two approaches have incomparable coverage |
| 9 | MINOR | §3(i) (a) "asked, if its report is silent" | Who asks, which instance, with what prompt, recorded where: all unspecified. Referees are fresh-context instances that no longer exist |
| 10 | MINOR | §3(i) (e) | "Drafted … in scratch" cannot be verified (adversarial m3). "Proof" is undefined (route? blueprint assembly? bridges? a referee's scratch, lessons 24?) |
| 11 | MINOR | §3(i) opening | "Test layer" and "sanity theorems" are undefined. API3's defective sanity theorems sit inside the stamped statement file |
| 12 | MINOR | CONTRIBUTING step 2 vs exception; lessons 33 | The exception is reached only by breaking step 2 (named `def`s) or lessons 33 (conditional form plus plant before the stamp). Step 2 should be amended instead or as well |
| 13 | MINOR | §3(i) (c) "recorded under `docs/replay/plants/`" | Sources only. No compiler output, command, toolchain or commit is required; the API3 plant directory holds sources without outcomes for M2 |
| 14 | MINOR | §3(i) (d) | Lists only "weakens a hypothesis". The complementary undetectable class "strengthens the conclusion" (`FamilySanity2.lean:11`) is missing; the per-statement list lives in docstrings, not in "the answer file" |
| 15 | MINOR | memo:4-5, 86-89 | Plans to append "Lead's changes" to the referee's report file, which breaks "Reports go verbatim under `review/`" |
| 16 | NOTE | §3(i) scope | Unclear whether the exception covers a test-layer MAJOR raised post-proof (step 10). Read literally, (e) cannot hold then, and step 5's fallback does not govern step 10 |
| 17 | NOTE | `docs/STATUS.md:33` | Says "sanity layer MAJOR answered", although answers M3 says the documents no longer call it "answered" |
| 18 | NOTE | memo §2 other rows | Checked and correct (details in §D) |

## A. Loopholes

**A1 (finding 3; MAJOR). Checking after the fact makes the fallback toothless.** Scenario: a careless or bad-faith lead meets
(a) and writes a thin (b)/(c) before the proofs. It stamps (e) and proves the batch. The adversarial referee (f) finds that (c)
failed for most statements. The last sentence now requires "a new statement". The memo itself argues (§3(ii), "Consequences")
that a re-freeze of an already proved statement "buys rule compliance, not an order claim". The lead therefore has a
ready-made argument for a waiver. API3 is exactly this case: (b) and (c) were incomplete before the proofs, and the remedy now
proposed is a waiver. Also, the fallback sentence lists "(a)–(e)" and omits (f), so not giving the post-proof referees the
finding has no consequence. Fix: verification by a fresh referee before any proof, inside the stamped tree; fallback over
(a)–(f) (text in §F.1, (f)).

**A2 (finding 4; MAJOR). (b) admits the restated hypothesis again.** (b) asks only that a sanity theorem "takes the constant
itself as a hypothesis and applies it to data". Nothing stops the theorem from taking the constant's other hypotheses as its
own assumptions, restated, and passing them through. Nor must it conclude the constant's conclusion on the data: a theorem
`(h : XStatement) : True := trivial`-adjacent forms meet the letter. This is live in the repository:
`nonStationaryLocal_family` (`OscInt/Front/FamilySanity2.lean:72-77`) takes `K`, `hK : IsCompact K` and `c`, `hc` as
assumptions, and carries the gradient condition `(∀ k ∈ K, c ≤ ‖fderiv ℝ (disp σ) k + L‖)` as a hypothesis restated in its
own type. On those features the theorem tests a restatement, not data. A plant in that body is caught (if at all) only because
the stated type no longer matches the proof term, which is brittleness, not separation. Fix: in (b), allow only statement
constants as hypotheses, discharge every hypothesis of the constant by proof on closed data, state the constant's conclusion,
and keep a per-feature table (§F.1 (b)).

**A3 (finding 5; MAJOR). (c) can be met without testing anything the finding names.** (c) requires "at least one planted
copy" per statement, chosen by the lead, and counts any rejection. Adversarial m4 already showed that each "rejected" in the
API3 record is a type mismatch of the existing proof term, so any syntactic edit, harmless or not, is rejected the same way.
A lead can therefore plant a trivial mutation (a changed numeral) for each statement and meet (c), while the plants the
referee named stay untested. The API3 record shows the same pattern in a milder form: the plants the five `FamilySanity2`
docstrings list as "caught" (e.g. `S ⊆ V` reversed, `K ⊆ U` reversed, `IsOpen V ↦ IsCompact V` at `FamilySanity2.lean:67-69`)
were never compiled as plants. The plant directory holds only the S3c, FE-S2.2l and S2.2F plants. Fix: cover every plant the
finding names plus one chosen by a referee. Count a rejection only if it falls at the mutated hypothesis or at the conclusion.
Add a Lean proof that the planted hypothesis is false on the data, the semantic half that `examples/consumer/ConsumerLocalChecks.lean`
supplied for some API3 plants (§F.1 (c)).

**A4 (finding 6; MAJOR). The class of plants that most changes what a statement says is waved through.** Both API3 referees
named plants that weaken a hypothesis. B named `V ×ˢ U ↦ S ×ˢ K`, a dropped `p ∈ K′`/`L ∈ K′`, and `K ⊆ U` reversed
(`pre-proof-B.md:87-92`). A named `∀ σ ∈ S ↦ ∀ σ ∈ V` and `S ⊆ V ↦ V ⊆ S` (`pre-proof-A.md:106`). The memo's (d) only asks
that such plants be listed and "left to the fidelity reviews". But (a) already requires those reviews to have passed, so
nothing new guards this class. A weakened hypothesis yields a statement stronger than `docs/statements.md`. If false, the proof
attempt would catch it; if still true (a redundant or reshaped hypothesis), it is proved and differs from the docs. Under the
current rule, a re-freeze with bundled `def`s plus the bite instances of step 2 and lessons 17 (`¬ Hyp` on bite data) detects
this class by machine. The conditional form cannot do so semantically (`FamilySanity2.lean:9-12` says so). This is the
strongest scenario under question A. A lead uses the exception on a finding whose named plants are mostly of this kind,
lists them under (d), and the batch keeps statements whose hypotheses no machine check has bitten. Fix: the exception does not
apply when the finding names such a plant (§F.1 (d)). Consequence, to be stated plainly to the owner: under that fix API3
would not qualify, and its record rests on the waiver alone.

**A5 (finding 7; MAJOR). (a) lets a statement that does not say what the docs say count as "faithful".** The repository uses
FAITHFUL-STRONGER/WEAKER mostly against the classical source or the brief (e.g. `review/2026-11-06-S4-pre-proof-B.md:7,19`;
`2026-11-06-S4b-post-proof-B.md:81`). (a) does not say against what. Read against `docs/statements.md`, a FAITHFUL-WEAKER
verdict is precisely "the Lean statement says less than the docs". The exception would then waive a re-freeze for a batch
containing it. Fix: FAITHFUL against `docs/statements.md`; a qualifier only against the classical source.

**A6 (finding 9; MINOR). The test-layer classification is decided by the lead in practice.** "Neither referee (asked, if its
report is silent) objects" names no asker, no prompt, no record. A blind referee is a fresh-context instance and cannot be
re-asked. A new instance must be prompted, and a leading prompt ("the statements are fine, agree this is only about tests?")
decides the outcome. In API3 neither referee was asked. Referee B's report is not silent: its prescribed fix is "bundle each
hypothesis as a named `def` used by both the statement and the sanity theorem" (`pre-proof-B.md:107-110`), i.e. a re-freeze.
The disagreement clause ("If the lead and a referee disagree") then cannot fire, because no referee is consulted. Fix in
§F.1 (a).

**A7 (finding 12; MINOR). The exception rewards skipping step 2.** Step 2 already requires named hypothesis `def`s shared with
the sanity theorems (`CONTRIBUTING.md:32-33`, lessons 11). Lessons 33 now allows the conditional form instead, with "at least
one planted copy per statement before the stamp". A batch that follows either never receives this MAJOR. The exception is
needed only by a batch that broke step 2 or lessons 33, and it makes breaking them cheap: author inline, take the MAJOR, answer
after review. Fix: amend step 2 to codify lessons 33 (both forms allowed, plants before the stamp), and make the exception's
use a recorded deviation, not a path. Suggested step 2 sentence in §F.3.

## B. Checkability, clause by clause

- **(a)** Verdicts and the absence of a MAJOR against the text can be checked from the verbatim reports under `review/` and
  the review stamp that covers them. The "objects / asked" part has no evidence trail: no prompt or verbatim answer is
  required. **Missing:** a committed prompt and verbatim answer.
- **(b)** Coverage can be checked mechanically (grep for `(h : XStatement)` per constant; I did this: 5 constants at 7bb4579,
  10 at bbafeeb). "Separating each feature the finding names" is judgment, and there is no feature→theorem→data map to check
  it against. Pass-through assumptions (A2) are invisible to a grep. **Missing:** the per-feature table; a rule against
  non-constant hypotheses (then checkable lexically from the signature).
- **(c)** A third party can recompile the sources, since Lean is deterministic at the pin. But the clause requires no outcome
  record, command, toolchain or commit. At bbafeeb the M2 plants (`Kprime-binder`, `univ-binder`, `ok-binder`) have sources
  and no recorded outcome. The 2026-11-08 record (`docs/replay/2026-11-08-API3-sanity-plants.txt`) has only the first four
  plants, and it lives outside `docs/replay/plants/`. Rejection "by these theorems" cannot be told apart from brittleness
  unless the error location is recorded. **Missing:** outputs, error location, and a falsity proof for each planted
  hypothesis.
- **(d)** Checkable by reading the answer file.
- **(e)** The repository part can be checked: the stamp manifest lists the files and their SHA-256 hashes (I checked that
  `stamps/20261108T010546Z-7bb457958327/manifest.txt` contains `FamilySanity.lean`, the plant record and `docs/proof-API3.md`,
  and no proof file). The RFC 3161 time bounds the stamp. A proof commit descending from the stamp-pin commit was created
  after the stamp hash existed (its hash includes the parent's), so "no proof committed before the stamp" is verifiable.
  "Not drafted in scratch" is not verifiable (adversarial m3, lessons 23, 29). **Missing:** nothing can make the scratch part
  checkable, so the clause must be worded at the strength the evidence has.
- **(f)** Checkable from `review/prompts/` and the adversarial report. **Missing:** a requirement that the adversarial
  referee's statement on (a)–(e) is a labelled section, and a consequence if (f) is not done.
- **Last sentence ("recorded in STATUS rows")** Checkable. "Disagree" leaves no record unless (a)'s question is recorded.

## C. Ambiguity

1. **"Test layer"** is used in the heading and in (a) before any definition. Does it include bite instances (step 2), the
   in-file sanity theorems of the stamped statement file (API3's are in `OscInt/Statements/Family.lean`), statement
   docstrings (adversarial n1: the frozen docstrings overstate the bites), the Challenge file, or `docs/statements.md`
   clarifications? Two careful readers differ on docstrings and on in-file sanity theorems.
2. **"Feature the finding names"** Findings name plants, often as examples ("e.g.", `pre-proof-A.md:128`). Is each example a
   feature, and does a feature named for S2.2F bind FE-S2.1L? (b) reads "every statement constant … separating each feature",
   which taken literally demands every feature on every constant.
3. **"Planted copy"** The procedure is undefined: a copy of the body under a new name, compiled against a copy of the sanity
   theorem with the hypothesis type replaced (what the record header describes). "Rejected" is undefined: any error, or an
   error at the discharge?
4. **"Strengthens a hypothesis or weakens the conclusion"** is a semantic direction, but many mutations are neither or
   incomparable: `K ⊆ U` reversed, `S ⊆ V ↦ V ⊆ S`, a swapped index. Readers will classify them differently, and the
   classification decides whether (c) or (d) governs.
5. **"Drafted … in scratch"; "any proof"** Does a route (`docs/proof-*.md`, drafted in scratch during the API3 review window),
   a blueprint assembly `x_of` (step 6, which is proof code of type `XStatement` from hypotheses), a bridge, or a referee's
   private proof (lessons 24) count?
6. **"Each referee"; "the adversarial referee"; "the answer file"; "batch"** None is defined in CONTRIBUTING. I read them as
   the two pre-proof referees of step 5, the step-10 adversarial referee, the pre-proof answers file, and the set of
   constants under one stamp, but the text should say so.
7. **"FAITHFUL-STRONGER / FAITHFUL-WEAKER"** Against what (A5)?
8. **Scope:** step 5 only, or also a test-layer MAJOR from a post-proof referee (finding 16)?

## D. The memo's facts (§2) and the waiver

What I checked, row by row:
- 9d03130 holds the statements; `git diff 9d03130 bbafeeb -- OscInt/Statements Challenge` is empty. **Correct.** (I did not
  run `make commit`.)
- e42dcd3 adds `stamps/20261108T002603Z-9d03130c8f3a/` (three `.tsr` files, two `.ots`) and the pins. **Correct.**
- 7bb4579 `FamilySanity.lean`: the constants taken as hypotheses are `FamilyCkOfUncurryStatement`, `FoldCritStatement`,
  `FoldOnStatement`, `StationaryPhaseFamilyStatement`, `StationaryPhaseOnStatement`, i.e. C10, S3c, FE-S3l, S2.2F, FE-S2.2l:
  **5 of 10, correct**. The plant record has 4 plants rejected and 2 unplanted copies accepted, for S3c and FE-S2.2l: **2 of
  10, correct**.
- 06c3c66 adds stamp `20261108T010546Z-7bb457958327`. Its manifest contains the sanity file, the plant record and the route,
  and no proof file. **Correct.**
- 3b05946 and a638f70 hold the proofs; 11a9ecf holds the replay record. **Correct** as git order (I did not open the replay
  record).
- ff5b80e `FamilySanity2.lean` covers NonStationaryLocal, StationaryPhaseLocal, FoldLocal, D4BoundLocal and NonStationaryOn,
  so 10 of 10 have a conditional theorem. **Correct.** "M2 plants rejected (second part of the plant record)" is **false**:
  `git log -- docs/replay/2026-11-08-API3-sanity-plants.txt` shows a single commit (7bb4579), the file has 33 lines and one
  part at bbafeeb, and `git grep "second part"` finds only the memo and the answers. ff5b80e added the plant sources
  `docs/replay/plants/2026-11-08-API3/{Kprime,univ,ok}-binder.lean.txt` (copies of `FamilySanity2` with only S2.2F renamed
  `PStationaryPhaseFamilyStatement`); the outcome appears only in the ff5b80e commit message. (finding 2)
- "FAITHFUL ×2 before, FAITHFUL ×2 after" is **correct** (`pre-proof-A.md:18-29`, `pre-proof-B.md` table,
  `post-proof-A.md:5,129`, `post-proof-B.md:159-161`).

**The waiver** ("met (a), (d) and (f), but (b) and (c) only after the proofs (5 of 10 constants and 2 of 10 plants before them,
all after)") is not at the strength of the evidence (finding 1):
- **(a)** The verdict part held. The "neither referee objects" part did not: neither was asked, and B's prescribed fix is a
  re-freeze (A6). At best "half met".
- **(c)** "All after" is false. At bbafeeb planted controls exist for **3 of 10** statements: S3c, FE-S2.2l (7bb4579) and
  S2.2F (ff5b80e). None exists for C10, FE-S3l, FE-S2.1L, FE-S2.2L, FE-S3L, FE-S4.1′L or FE-S2.1l. The record under
  `docs/replay/plants/` has sources only.
- **(d)** Met only after the proofs, and only in part. The pre-proof answers (stamped) list three uncaught plants and do not
  mention the weakening class. The generic limit appears in the post-proof answers (ff5b80e, `answers.md:21-25`); the
  per-statement lists are in the `FamilySanity2` docstrings, not in "the answer file".
- **(e)** Not mentioned. It held only for what existed before the proofs: 5/10 theorems, 2/10 plants, plant sources not
  committed (they were in the session scratchpad until ff5b80e, adversarial m4).
- **(f)** The post-proof referees were given the finding and the answer (`review/prompts/API3-post-proof.md:7-12,25`), and the
  adversarial referee was asked about the departure (`API3-adversarial.md:20-23`). It could not, and did not, state whether
  (a)–(e) held, because they did not exist. It found M1 and M2, i.e. that (b) and (c) failed. "Met" is wrong. "The
  adversarial referee judged the departure (M3) and found (b), (c) incomplete (M1, M2)" is right.

## E. Is (i) defensible against (ii)? The harshest competent objection

"You are asked to ratify a rule and, in the same act, exempt from it the only case that motivated it. That case fails four of
its six conditions, even after the proofs, on the memo's own wording. The rule's guards run after the proofs, when its
fallback is the one the memo calls worthless. Its machine evidence ((b), (c)) is shown by the batch itself to be meetable by
restated assumptions and brittle proof terms. And its own clause (d) concedes that the class of plants which makes a statement
say more than the docs is not checked by machine at all, while def-bundling with bites checks it. The memo's claims that the
substitute is 'strictly stronger … for the plants it covers' and that (ii) makes 'no claim stronger' are true only after
removing the plants it does not cover. (ii) would put the lessons-11 bite check on exactly the plants the referees named. What
(ii) cannot buy is the order claim, and that is already lost for API3 in either option, because the waiver records that (b)
and (c) came after the proofs. A general exception adopted to absorb a one-time deviation is the 'weakened rule to get green'
that CONTRIBUTING forbids."

My assessment. The objection is right on the rule's design (A1–A4) and on the memo's comparative wording (finding 8). It is
weaker on the bottom line. For API3, both options leave the order claim at the same strength. (ii) adds machine bites for the
weakening class on ten statements that are already proved and judged faithful four times. (i) adds nothing and costs nothing.
**A one-time waiver honestly worded (§F.2) is defensible**, and is the right core of (i). **The general exception is
defensible only with the §F.1 changes.** Without them, it should not be adopted; the honest alternative is "keep step 5 as is,
record the API3 waiver, amend step 2 (§F.3) so the MAJOR does not recur". The memo should offer the owner this option (iii)
explicitly. Its §4 sentence should read: "the substitute and def-bundling cover different plants: the conditional form tests the
frozen text for plants that make a hypothesis harder to discharge; def-bundling with bite instances also tests plants that
weaken a hypothesis; (ii) would add the latter for API3 but cannot restore the order claim."

## F. Required changes (exact text)

### F.1 Replacement for the rule text in memo §3(i)

> Reports go verbatim under `review/`. A BLOCKER or MAJOR against what a statement says means a new statement (back to
> 2), never an edit. **Test-layer exception.** Here the *test layer* of a batch (the statement constants under one stamp) is
> its sanity theorems and bite instances (step 2), wherever they are written; it does not include any `def …Statement`
> body, any docstring in a stamped file, or `docs/statements.md`. A MAJOR from a blind pre-proof referee of this step whose
> subject is only the test layer, and not the meaning or truth of any statement, may be answered without a re-freeze only
> if all of (a)–(f) hold before any proof code for any statement of the batch is committed (proof code: any Lean proof whose
> type is, or is assembled into, a statement constant of the batch, including blueprint assemblies and bridges):
> (a) each of the two pre-proof referees gives every statement of the batch the verdict FAITHFUL against
> `docs/statements.md` (a STRONGER or WEAKER qualifier counts only against the classical source) and raises no BLOCKER or
> MAJOR against any statement text; and for each report, either the report itself says the finding concerns only the test
> layer, or a fresh referee, given that report, the statement file and `docs/statements.md` and asked the neutral question
> "does this finding concern what any statement says, or only its tests?" (prompt committed under `review/prompts/`, answer
> verbatim under `review/`), answers "only its tests";
> (b) every statement constant of the batch has at least one sanity theorem whose only hypotheses are statement constants
> of the batch, which discharges every hypothesis of the constant by proof on explicit, closed data and concludes the
> constant's conclusion on those data; the data are generic (lessons 17): every set the statement quantifies over is
> nonempty, and the roles, signs and indices the finding names take values that separate them; the answer file has a table
> mapping, per statement, each plant or feature the finding names to the theorem and data that separate it;
> (c) for each plant the finding names, and for one further plant per statement chosen by a referee or fixed in a prompt
> committed before the answer, a copy of the frozen body with exactly that mutation, compiled in place of the constant
> against an unchanged copy of the sanity theorem, fails to elaborate at the discharge of the mutated hypothesis or at the
> conclusion, and the unmutated copy compiles; a Lean proof that the mutated hypothesis is false on the data accompanies
> each such plant; sources, exact compiler output, command and commit are committed under `docs/replay/plants/<date>-<batch>/`;
> (d) the finding names no plant that weakens a hypothesis or strengthens the conclusion (the conditional form cannot detect
> these); the answer file lists, per statement, the kinds of plants the theorems cannot detect and says that these rest on
> the fidelity reviews alone;
> (e) the answer, the sanity files, the plant record and the report of (f) are committed and covered by a stamp
> (`make stamp`), and the order claim is worded as in lessons 29 ("no proof committed before the stamp at …; that none
> existed in scratch rests on the lead's statement");
> (f) a fresh referee who has seen no proof of the batch states, in a report committed under `review/`, for each of (a)–(e),
> whether it held, with the evidence.
> If the lead and a referee disagree on whether a finding concerns only the test layer, or if any of (a)–(f) fails, the
> rule above applies: a new statement. The post-proof referees (step 10) are given the finding, the answer and the report of
> (f). This exception does not apply to findings raised after any proof code exists. Each use is recorded in the batch's
> STATUS rows.

(Note to the owner: (d) as amended excludes API3. That is intended; API3 is handled by the waiver.)

### F.2 Replacement for the waiver sentence

> "API3 answered a test-layer MAJOR without a re-freeze before any exception existed. Against the conditions later adopted:
> (a) both pre-proof referees judged all ten statements FAITHFUL with no MAJOR against the text, but neither was asked
> whether the finding was test-layer only, and referee B's proposed fix was bundled `def`s (a re-freeze); (b) held for 5 of
> 10 constants before the proofs and 10 of 10 after (ff5b80e); (c) held for 2 of 10 statements before the proofs and for 3 of
> 10 (S3c, FE-S2.2l, S2.2F) at <commit>, with the S2.2F outcomes recorded only in the ff5b80e commit message; (d) only after
> the proofs; (e) only for the partial layer above (stamp `20261108T010546Z-7bb457958327`); (f) the post-proof referees had
> the finding and the answer, and the adversarial referee judged the departure (M3) and found (b) and (c) incomplete (M1, M2).
> The hypothesis-weakening plants the referees named (e.g. `V ×ˢ U ↦ S ×ˢ K`, a dropped `p ∈ K′`) rest on the fidelity
> reviews alone. Ratified by the owner on <date> as a one-time waiver."

If the owner wants (c) to read "all after", the lead must first add plants (sources, outputs, falsity proofs) for the seven
uncovered statements and record them. Until then the sentence above is the accurate one.

### F.3 Step 2 (prevents recurrence; finding 12)

Replace "Hypotheses are named `def`s shared by the statement and its sanity theorems (lessons 11)." by:

> "Each hypothesis is either a named `def` shared by the statement and its sanity theorems, with a bite instance proving its
> negation on data (lessons 11, 17), or tested by a sanity theorem that takes the statement constant as its only hypothesis
> and discharges it on generic data (lessons 33); in the second form at least one planted copy per statement is run and
> recorded under `docs/replay/plants/` before the stamp."

### F.4 Other edits

- memo:25 and `review/2026-11-08-API3-answers.md:29`: replace "(second part of the plant record)" by "(plant sources in
  `docs/replay/plants/2026-11-08-API3/{Kprime,univ,ok}-binder.lean.txt`; outcome stated in the ff5b80e commit message, not
  recorded in a replay file)". Or record the outcome and then cite it.
- memo §4: replace "the substitute is strictly stronger than def-bundling for the plants it covers, and (ii) costs half a
  session without making any claim stronger" by the sentence at the end of §E, and add option (iii) (no general exception;
  waiver plus step-2 amendment).
- memo §5: put the lead's changes in `review/2026-11-08-step5-rule-answers.md`, not at the end of the referee's report
  (verbatim rule, finding 15).
- `docs/STATUS.md:33`: "sanity layer MAJOR answered" → "sanity layer MAJOR addressed by conditional sanity theorems (owner
  decision …)", to match answers M3 (finding 17).
