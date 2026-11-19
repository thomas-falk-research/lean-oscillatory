<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Funding and access calls: what is open, verified from official pages (2026-11-16)

Status: findings only; nothing has been submitted and nobody has been contacted. The owner decides and submits.
Method: a web sweep by a fresh-context agent (108 page reads and searches, all on 2026-11-16), then a second,
separate fetch of the two call pages that matter by another agent. Labels: CITED-READ (the official page was opened
and the text seen in this session), SECONDARY (seen only on a third-party page), NOT FOUND. Both agents and the lead
are instances of the same model family; "second fetch" means a second read of the page, not an independent human
check. Dates below are quoted from the pages.

## The call that closes in about two weeks

Three EuroHPC Joint Undertaking access calls share one cut-off: **1 December 2026, 10:00 CET**. Each is a monthly
cut-off of a continuously open call ("Deadline model: Multiple cut-off"), with a technical assessment by the hosting
site and no peer review, first come first served. CITED-READ twice for the first two.

| Call | Deadline string on the page | What it gives | Fit for OscInt |
|---|---|---|---|
| Quantum Access Pilot Mode (reference "QUANTUM ACCESS PILOT MODE"; opened 25 June 2026; portal call 61) | "1 Aug 2026, 10:00 / 1 Sep 2026, 10:00 / 1 Oct 2026, 10:00 / 1 Nov 2026, 10:00 / 1 Dec 2026, 10:00 / 31 Dec 2033, 10:00 (CET)" | 1 to 25 QPU hours on one of six systems for 3 or 6 months; access "up to 2 weeks after the cut-off date" | Good for a pre-registered hardware test of a machine-checked prediction (a continuous-time quantum walk on a chain or ring of qubits) |
| Development Access (reference "EUROHPC JU CALL FOR PROPOSALS FOR DEVELOPMENT ACCESS MODE"; portal call 42) | "… 1 Nov 2026, 10:00 / 1 Dec 2026, 10:00 / 31 Dec 2033, 10:00 (CET)" | 400 to 4,500 node-hours per partition for up to 12 months; scope "code and algorithm development, development of workflows" | Moderate: certified interval computations and proof replays are CPU workloads, but small by HPC standards (see "Candour") |
| Benchmark Access (portal call 41) | "… 1 Nov 2026, 10:00 / 1 Dec 2026, 10:00 / 31 Dec 2033, 10:00 (CET)" | 200 to 3,500 node-hours for 3 months | Weaker: meant to prepare a Regular or Extreme Scale application |

Quantum systems and request ranges, read by the sweep agent from the table image on the call page (image dated
2026-10 in its address; CITED-READ once, from an image, so re-read it on the page before relying on a number):

| System | Site | Technology | Topology | Maximum (minimum) QPU hours |
|---|---|---|---|---|
| Euro-Q-Exa | LRZ, Germany | digital, superconducting | "Crystal" | 10 (1) |
| VLQ | IT4Innovations, Czechia | digital, superconducting | star with a central resonator | 10 (1) |
| Lucy | GENCI/CEA, France | digital, photonic | all-to-all | 25 (10) |
| Piast-Q | PCSS, Poland | digital, trapped ions | all-to-all | 25 (10) |
| Ruby | GENCI/CEA, France | analogue simulator, neutral atoms | 2D array | 25 (10) |
| EuroQCS-Spain | BSC, Spain | analogue (annealer) | not applicable | 25 (10) |

The page carries a notice that EuroQCS-Spain is in maintenance from end-November to end-December.

## Eligibility (the open question the owner must settle before drafting further)

- Quantum pilot. Access Policy version 2025.12, section 4.2.2: "users residing, established or located in a Member
  State or a third country associated to the Digital Europe Programme or to Horizon Europe"; the call page says it is
  "meant for all categories of users". No applicant guide is published for this call. CITED-READ.
- Development and Benchmark Access. "Information for Applicants" (PDF created 2026-08-24): "Researchers from academia,
  research institutes, public authorities and industry established or located in an EU Member State or in a country
  associated to the Digital Europe Programme or to Horizon Europe". For a research organisation or a company, "the
  project leader has an employment contract … valid for at least 3 months after the end of the allocation period";
  a company must use the resources "solely for open Research and Development (R&D) purposes". CITED-READ.
- **NOT FOUND:** whether a natural person with no employing organisation may apply. The texts name organisations and
  an employment contract; they neither admit nor exclude an unaffiliated individual. This decides whether an
  application is possible at all, and only the owner knows the applicant's country and legal form
  (`[APPLICANT-COUNTRY]`, `[APPLICANT-LEGAL-FORM]`). The pages give no e-mail address; the sweep agent's report names
  an access address that the second fetch did not find on either page, so it is not repeated here. The site-wide
  contact page is linked from both call pages.

## What must be submitted

- A "light access request" entered in the EuroHPC access portal (calls 61 and 42). The form sits behind a login and
  could not be read: **field names, character limits and required attachments are NOT FOUND.** The owner has to log in
  and copy the field list before the drafts can be cut to size.
- Development Access asks, per its Information for Applicants, for "a detailed description of the challenges hindering
  the scalability of the code", "a clear plan for code development", and that "the available human resources and
  expertise … must be quantified". The only template published is the final report.
- Evaluation criteria: a technical assessment of "the pertinence and feasibility of the request for the targeted
  system" by the hosting site. No scores or weights are published. Obligations: a final report (within three months
  for Development Access), an acknowledgement text, and publication of the project leader's name and affiliation.
- No data management plan is requested by either call (the drafts in this folder include one because the owner asked
  for it and because it documents what the project already does).

## Other calls, with their deadlines

| Call | Deadline | Why it is or is not a fit | Label |
|---|---|---|---|
| EuroHPC AI for Science and Collaborative EU Projects | 11 December 2026, 10:00 CET | AI workloads; peer-reviewed | CITED-READ |
| EuroHPC Large Scale Access to AI Factories | 30 November 2026, 10:00 CET | industry only, more than 50,000 GPU hours | CITED-READ |
| Six EuroHPC quantum research and innovation calls (HORIZON-JU-EUROHPC-2026-…) | 17 November 2026, 17:00 CET | consortium actions of EUR 15 to 24 million | CITED-READ (news page; the Funding and Tenders portal pages did not render) |
| Chips JU calls | 1 and 8 December 2026 | large consortium actions | CITED-READ |
| NLnet Restack, second call | 3 January 2027, 12:00 CET | EUR 5,000 to 50,000, individuals accepted; scope is the open internet stack, so the thematic fit is doubtful; the proposal form showed a "missed the deadline" message on the day of the sweep | CITED-READ, with that conflict |
| ERC Consolidator Grant | 12 January 2027 | individual grant with a host institution; a different scale of proposal | CITED-READ |
| EuroHPC Quantum Machine Learning call | 28 January 2027 | topic not ours | CITED-READ |
| EIC Pathfinder Open, stage 1 | 25 February 2027 | at least three entities | CITED-READ |
| Horizon Europe Cluster 4, 2027 calls | 18 March 2027 | no quantum-software or formal-verification topic found in the work programme | CITED-READ (work programme PDF) |
| HORIZON-INFRA-2027 | 15 June 2027 | research-infrastructure consortia | CITED-READ (work programme PDF) |
| AI for Math Fund seed grants (Renaissance Philanthropy; not an EU programme) | rolling | up to USD 100,000; the strongest thematic match found | CITED-READ |
| NGI0 Commons Fund | closed (final call 1 June 2026) | — | CITED-READ |
| QuantERA | no 2026 or 2027 call found | — | NOT FOUND |

No 2027 cut-off is published yet for any EuroHPC access mode: every list ends in December 2026, followed by a
placeholder date in 2033. The Access Policy says "Monthly cut-offs (12 cut-offs per year)", so a missed cut-off
PLAUSIBLY costs one month, but that is not confirmed.

## Hardware routes that need no call

| Route | Terms as published | Label |
|---|---|---|
| IBM Quantum Open Plan | free, "up to 10 minutes per 28-day rolling window"; instances only in the us-east region; pay-as-you-go from USD 96 per minute | CITED-READ |
| Quantum Inspire (QuTech) | free registration, superconducting back ends; limits not stated on the landing page | CITED-READ |
| AWS Braket | pay per task and shot (for example IQM Garnet USD 0.00145 per shot plus USD 0.30 per task) | CITED-READ |
| IQM Resonance | a free starter tier of 30 credits per month | SECONDARY (the official page returned an error) |
| Quandela Cloud (photonic) | registration open; no free-tier figure on the page | CITED-READ |
| Pasqal Cloud | free plan covers emulators only | CITED-READ |

No open, individual-accessible route to a coupled-waveguide-array device was found; a waveguide test needs a partner
laboratory.

## Recommendation

1. Apply to the **Quantum Access Pilot** at the 1 December cut-off, for Euro-Q-Exa (1 to 10 QPU hours, minimum 1), with
   one concrete, pre-registered experiment. It is the only route found that is free, light, and gives EU hardware.
2. Apply to **Development Access** at the same cut-off only if the certified-computation work plan in this folder
   justifies the node-hours honestly; otherwise wait a month.
3. Both depend on the eligibility answer above. If an unaffiliated individual cannot apply, the fallbacks are the IBM
   Open Plan (enough for a small pilot of the same protocol) and the rolling AI for Math Fund.

## Candour: the strongest case against applying now

- OscInt's own compute need is small: the full replay is about 12 core-hours. A request for thousands of node-hours
  must rest on new certified-computation work that does not exist yet; a hosting site may judge it a poor fit for a
  call about scaling HPC codes.
- The physics a quantum-walk run would test (Bessel-function spreading on a chain) has been confirmed in many
  laboratories since 2008. The new part is the trust chain (machine-checked statement, certified enclosure, registered
  protocol), not the physics; a reviewer may see a device benchmark rather than science.
- The form was not seen, the systems table was read once from an image, and no hardware calibration data for
  Euro-Q-Exa has been read yet. Until they are, the resource numbers in these drafts are placeholders.
