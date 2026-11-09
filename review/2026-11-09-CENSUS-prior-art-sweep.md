<!-- Report of the prior-art and source sweep run 2026-11-09 by a fresh-context subagent (same model family as the lead). Verbatim except one substitution: on line 26 the agent's local path to its query log is replaced by the committed copy, review/2026-11-09-CENSUS-prior-art-querylog.tsv. The brief is not recorded (owner decision 2026-11-09: for this sweep, the report and the query log are the record; they suffice to verify every citation). Its corrections to the brief (e.g. Inui-Konishi-Konno, not Segawa; the Grover sign; the claim about stable 2D singularities) are its own findings. -->

# Prior-art and source-verification sweep: singularity census of 2D lattice dispersion relations

Date of sweep: 2026-11-09. All searches and verifications listed below were run in this session.

How things were verified:
- **[CR]**: bibliographic data checked against the Crossref record `api.crossref.org/works/<DOI>`.
- **[zb]**: data from the zbMATH Open record only, because no Crossref record was checked or none exists.
- **[arX]**: arXiv abstract page and/or full PDF read.
- Formulas are copied from the text I read (arXiv full text unless stated otherwise).
- Anything marked **(own derivation, not from a source)** is my algebra and is NOT a citation.

## 0. Coverage limits (read first)

- **Google Scholar:** not reachable (HTTP 403 from the proxy).
- **Crossref `query.bibliographic` search:** mostly rate-limited (HTTP 429). Only 2 of about 6 attempts succeeded. Crossref was therefore used for DOI verification; searching used arXiv (API and web search), zbMATH Open API, OpenAlex, the StackExchange API (MathOverflow), the GitHub code-search API and the Isabelle AFP index.
- The arXiv API was rate-limited twice. I switched to the arXiv web search, so each query was still run.
- **Paywalled texts not read** (bibliographic data verified only):
  - Schultz 1998, Semenoff 1984, Wallace 1947, Taflove–Hagness, LeVeque 2007, Patra–Karttunen 2006
  - David–Sagaut–Sengupta 2009, Arnold 1972/73, Varchenko 1976, Duistermaat 1974
  - The published (journal) versions of all arXiv papers. I read the arXiv versions.

## 1. Query log

The full machine log is at `review/2026-11-09-CENSUS-prior-art-querylog.tsv`; the table below is generated from it. The "Hits" column gives the number of results looked at and the total. Relevant hits are named in Sections 2–4.

**Attempts that failed and are not in the table:**
- Crossref `query.bibliographic`: 429 four times. Queries: "Borovyk Goldberg Klein-Gordon equation on Z^2 quantum harmonic lattice", "Schultz wave equation on the lattice in two and three dimensions", "Schultz wave equation lattice" (curl), "Wan Zhang Strichartz estimate discrete Schrodinger layered King's grid".
- OpenAlex search and Semantic Scholar search: 429.
- Google Scholar: 403.
- arXiv API: 429 for `all:"nine-point" AND all:Laplacian AND all:stencil` and `all:"9-point" AND all:Laplacian AND all:isotropic`.
- Publisher pages:
  - ScienceDirect (David et al.): 403
  - APS abstract page (Semenoff): 403, abstract obtained via OpenAlex
  - Springer (Arnold 1972): 429
  - LeVeque exercise files: 403
- GitHub repos API: 403. Repository READMEs were read via raw.githubusercontent.com instead.

Note on the hit counts: Crossref "total" counts are the sizes of Crossref's relevance-ranked result sets, not real matches.

| # | Date | Engine / database | Exact query or record | Hits (shown / total) |
|---|---|---|---|---|
| 1 | 2026-11-09 | zbMATH Open API | `Varchenko Newton polyhedra` | 5 shown / 23 total |
| 2 | 2026-11-09 | arXiv API | `au:Cuenin AND au:Ikromov` | 1 shown / 1 total |
| 3 | 2026-11-09 | arXiv API | `ti:"discrete Klein-Gordon" AND abs:decay` | 2 shown / 2 total |
| 4 | 2026-11-09 | arXiv API | `au:Borovyk AND au:Goldberg` | 1 shown / 1 total |
| 5 | 2026-11-09 | arXiv API | `au:Schultz AND ti:lattice` | 7 shown / 7 total |
| 6 | 2026-11-09 | arXiv API | `au:Stefanov AND au:Kevrekidis` | 10 shown / 13 total |
| 7 | 2026-11-09 | Crossref works/DOI | `10.1088/1361-6544/ac2b86` | 1 record |
| 8 | 2026-11-09 | Crossref works/DOI | `10.1088/0951-7715/18/4/022` | 1 record |
| 9 | 2026-11-09 | zbMATH Open API | `Borovyk Goldberg Klein-Gordon` | 1 shown / 1 total |
| 10 | 2026-11-09 | zbMATH Open API | `au:Schultz ti:wave equation lattice` | 1 shown / 1 total |
| 11 | 2026-11-09 | zbMATH Open API | `discrete Schroedinger equation dispersive estimates Z^2` | 3 shown / 3 total |
| 12 | 2026-11-09 | zbMATH Open API | `ti:discrete Klein-Gordon ti:decay` | 2 shown / 2 total |
| 13 | 2026-11-09 | Crossref works/DOI | `10.1016/j.matpur.2016.10.002` | 1 record |
| 14 | 2026-11-09 | Crossref works/DOI | `10.1002/(SICI)1097-0312(199806)51:6<663::AID-CPA4>3.0.CO;2-5` | 1 record |
| 15 | 2026-11-09 | arXiv API | `abs:"discrete Schrodinger" AND abs:"dispersive" AND abs:"two-dimensional"` | 0 shown / 0 total |
| 16 | 2026-11-09 | arXiv API | `abs:lattice AND abs:"dispersive estimates" AND abs:"Newton polygon"` | 0 shown / 0 total |
| 17 | 2026-11-09 | zbMATH Open API | `an:0928.35089 (review text)` | 1 record |
| 18 | 2026-11-09 | zbMATH Open API | `an:1378.35182 (review text)` | 1 record |
| 19 | 2026-11-09 | zbMATH Open API | `an:1476.35133 (review text)` | 1 record |
| 20 | 2026-11-09 | arXiv PDF full text | `2011.12076` | 1 document |
| 21 | 2026-11-09 | arXiv PDF full text | `1304.6353` | 1 document |
| 22 | 2026-11-09 | arXiv PDF full text | `nlin/0409009` | 1 document |
| 23 | 2026-11-09 | arXiv API | `abs:"discrete Schrodinger" AND abs:"Z^2" AND abs:decay` | 0 shown / 0 total |
| 24 | 2026-11-09 | arXiv API | `ti:dispersive AND ti:lattice` | 30 shown / 95 total |
| 25 | 2026-11-09 | arXiv API | `abs:"time decay" AND abs:lattice AND abs:"oscillatory integral"` | 4 shown / 4 total |
| 26 | 2026-11-09 | arXiv abs page | `2312.04130` | 1 record |
| 27 | 2026-11-09 | arXiv abs page | `2503.08996` | 1 record |
| 28 | 2026-11-09 | arXiv abs page | `2609.37300` | 1 record |
| 29 | 2026-11-09 | arXiv abs page | `2605.08372` | 1 record |
| 30 | 2026-11-09 | arXiv abs page | `1808.05714` | 1 record |
| 31 | 2026-11-09 | arXiv API | `au:Cheng_Jiawei AND (abs:lattice OR abs:discrete)` | 5 shown / 5 total |
| 32 | 2026-11-09 | arXiv API | `au:Hua_Bobo AND (abs:dispersive OR abs:decay)` | 6 shown / 6 total |
| 33 | 2026-11-09 | arXiv API | `au:Tadano AND abs:dispersive` | 3 shown / 3 total |
| 34 | 2026-11-09 | zbMATH Open API | `Bi Cheng Hua wave equation on lattices oscillatory integrals` | 2 shown / 2 total |
| 35 | 2026-11-09 | zbMATH Open API | `dispersive estimates discrete Schroedinger honeycomb lattice` | 1 shown / 1 total |
| 36 | 2026-11-09 | arXiv abs page | `2412.02947` | 1 record |
| 37 | 2026-11-09 | arXiv abs page | `2403.07445` | 1 record |
| 38 | 2026-11-09 | arXiv abs page | `2406.00949` | 1 record |
| 39 | 2026-11-09 | Crossref works/DOI | `10.1007/s00028-026-01205-x` | 1 record |
| 40 | 2026-11-09 | arXiv PDF full text | `2412.02947` | 1 document |
| 41 | 2026-11-09 | arXiv PDF full text | `2503.08996` | 1 document |
| 42 | 2026-11-09 | arXiv PDF full text | `2403.07445` | 1 document |
| 43 | 2026-11-09 | arXiv PDF full text | `2312.04130` | 1 document |
| 44 | 2026-11-09 | arXiv API | `abs:caustic AND abs:lattice AND (abs:"group velocity" OR abs:dispersion) AND abs:cusp` | 0 shown / 0 total |
| 45 | 2026-11-09 | arXiv API | `abs:"periodic graph" AND abs:"dispersive estimate"` | 1 shown / 1 total |
| 46 | 2026-11-09 | arXiv API | `abs:"discrete Schrodinger" AND abs:"dispersive" AND abs:"two dimensional"` | 0 shown / 0 total |
| 47 | 2026-11-09 | arXiv API | `au:Schippa AND au:Cuenin` | 1 shown / 1 total |
| 48 | 2026-11-09 | arXiv API | `abs:caustics AND abs:lattice AND abs:cusp` | 1 shown / 1 total |
| 49 | 2026-11-09 | arXiv API | `abs:discrete AND abs:Schrodinger AND abs:dispersive AND abs:decay AND abs:lattice` | 0 shown / 0 total |
| 50 | 2026-11-09 | arXiv abs page | `2107.13400` | 1 record |
| 51 | 2026-11-09 | arXiv API | `all:dispersive AND all:estimates AND all:lattice AND all:discrete` | 31 shown / 31 total |
| 52 | 2026-11-09 | arXiv abs page | `2507.20142` | 1 record |
| 53 | 2026-11-09 | arXiv abs page | `2609.34081` | 1 record |
| 54 | 2026-11-09 | arXiv abs page | `2609.05930` | 1 record |
| 55 | 2026-11-09 | arXiv API | `all:King AND all:grid AND all:Schrodinger` | 0 shown / 0 total |
| 56 | 2026-11-09 | arXiv API | `all:"next-nearest" AND all:dispersive AND all:decay` | 3 shown / 3 total |
| 57 | 2026-11-09 | arXiv API | `au:Wan_Zhiqiang AND au:Zhang_Heng` | 0 shown / 0 total |
| 58 | 2026-11-09 | zbMATH Open API | `dispersive estimate lattice Newton polyhedra` | 1 shown / 1 total |
| 59 | 2026-11-09 | zbMATH Open API | `discrete Schroedinger equation lattice decay estimate` | 10 shown / 10 total |
| 60 | 2026-11-09 | zbMATH Open API | `ti:quantum walk ti:dispersive` | 0 shown / 0 total |
| 61 | 2026-11-09 | Crossref works/DOI | `10.1007/s00526-025-03026-1` | 1 record |
| 62 | 2026-11-09 | Crossref works/DOI | `10.4208/jms.v58n4.25.03` | 1 record |
| 63 | 2026-11-09 | zbMATH Open API | `Cheng fourth-order Schroedinger equation on lattices` | 3 shown / 3 total |
| 64 | 2026-11-09 | zbMATH Open API | `Cuenin Schippa Fourier transform surface-carried measures generic surfaces` | 1 shown / 1 total |
| 65 | 2026-11-09 | zbMATH Open API | `Hong Yang uniform Strichartz estimates on the lattice` | 3 shown / 3 total |
| 66 | 2026-11-09 | Crossref works/DOI | `10.3934/cpaa.2022079` | 1 record |
| 67 | 2026-11-09 | Crossref works/DOI | `10.3934/dcds.2019134` | 1 record |
| 68 | 2026-11-09 | arXiv PDF full text | `2107.13400` | 1 document |
| 69 | 2026-11-09 | zbMATH Open API | `Erdos Salmhofer decay of the Fourier transform of surfaces with vanishing curvature` | 2 shown / 2 total |
| 70 | 2026-11-09 | arXiv API | `au:Chandrasekaran AND au:Betouras` | 6 shown / 6 total |
| 71 | 2026-11-09 | arXiv API | `au:Yuan_Noah AND au:Fu_Liang` | 0 shown / 0 total |
| 72 | 2026-11-09 | arXiv API | `all:"higher-order van Hove"` | 27 shown / 27 total |
| 73 | 2026-11-09 | arXiv API | `ti:"Magic of high order van Hove singularity"` | 1 shown / 1 total |
| 74 | 2026-11-09 | arXiv API | `au:Isobe AND au:Fu_L AND ti:van` | 0 shown / 0 total |
| 75 | 2026-11-09 | arXiv abs page | `1910.10183` | 1 record |
| 76 | 2026-11-09 | arXiv abs page | `2207.06099` | 1 record |
| 77 | 2026-11-09 | arXiv abs page | `1901.05432` | 1 record |
| 78 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevResearch.2.013355` | 1 record |
| 79 | 2026-11-09 | Crossref works/DOI | `10.1002/apxr.202200061` | 1 record |
| 80 | 2026-11-09 | Crossref works/DOI | `10.1038/s41467-019-13670-9` | 1 record |
| 81 | 2026-11-09 | arXiv PDF full text | `1910.10183` | 1 document |
| 82 | 2026-11-09 | arXiv API | `all:caustics AND all:lattice AND all:catastrophe` | 1 shown / 1 total |
| 83 | 2026-11-09 | arXiv API | `all:caustic AND all:"quantum walk"` | 1 shown / 1 total |
| 84 | 2026-11-09 | arXiv API | `all:caustics AND all:"light cone" AND all:lattice` | 1 shown / 1 total |
| 85 | 2026-11-09 | arXiv API | `ti:caustics AND (all:lattice OR all:quantum)` | 40 shown / 93 total |
| 86 | 2026-11-09 | arXiv API | `all:caustics AND all:"tight-binding"` | 4 shown / 4 total |
| 87 | 2026-11-09 | arXiv abs page | `2102.00288` | 1 record |
| 88 | 2026-11-09 | arXiv abs page | `1710.01289` | 1 record |
| 89 | 2026-11-09 | arXiv abs page | `2410.06803` | 1 record |
| 90 | 2026-11-09 | zbMATH Open API | `au:Ignat au:Zuazua` | 12 shown / 12 total |
| 91 | 2026-11-09 | Crossref works/DOI | `10.1137/070683787` | 1 record |
| 92 | 2026-11-09 | Crossref works/DOI | `10.1016/j.matpur.2012.01.001` | 1 record |
| 93 | 2026-11-09 | zbMATH Open API | `Zuazua propagation observation control numerical approximation waves` | 5 shown / 6 total |
| 94 | 2026-11-09 | zbMATH Open API | `Trefethen group velocity in finite difference schemes` | 4 shown / 4 total |
| 95 | 2026-11-09 | Crossref works/DOI | `10.1137/1024038` | 1 record |
| 96 | 2026-11-09 | zbMATH Open API | `ti:Propagation, observation, and control of waves approximated by finite difference methods` | 1 shown / 1 total |
| 97 | 2026-11-09 | Crossref works/DOI | `10.1137/S0036144503432862` | 1 record |
| 98 | 2026-11-09 | arXiv API | `all:Yee AND all:"numerical dispersion" AND all:caustic` | 0 shown / 0 total |
| 99 | 2026-11-09 | arXiv API | `all:"finite difference" AND all:"dispersive estimates" AND all:uniform` | 0 shown / 0 total |
| 100 | 2026-11-09 | zbMATH Open API | `numerical dispersion finite difference caustics` | 7 shown / 7 total |
| 101 | 2026-11-09 | zbMATH Open API | `dispersive estimates semidiscrete Schroedinger wave uniform mesh` | 0 shown / 0 total |
| 102 | 2026-11-09 | Crossref works/DOI | `10.1016/j.euromechflu.2008.04.002` | 1 record |
| 103 | 2026-11-09 | zbMATH Open API | `an:1153.76390 (review text)` | text withheld (licence) |
| 104 | 2026-11-09 | OpenAlex works/doi | `10.1016/j.euromechflu.2008.04.002 (abstract)` | record found, no abstract |
| 105 | 2026-11-09 | zbMATH Open API | `Taflove Hagness computational electrodynamics finite-difference time-domain` | 2 shown / 2 total |
| 106 | 2026-11-09 | zbMATH Open API | `Yee numerical solution initial boundary value problems Maxwell isotropic media` | 3 shown / 11 total |
| 107 | 2026-11-09 | arXiv API | `all:Yee AND all:"numerical dispersion relation" AND all:FDTD` | 1 shown / 1 total |
| 108 | 2026-11-09 | arXiv PDF full text | `1407.5253` | 1 document |
| 109 | 2026-11-09 | Web (author site) | `https://eecs.wsu.edu/~schneidj/ufdtd/ufdtd.pdf (Schneider, Understanding the FDTD Method)` | 1 document |
| 110 | 2026-11-09 | arXiv API | `all:FDTD AND all:"numerical dispersion"` | 16 shown / 16 total |
| 111 | 2026-11-09 | arXiv PDF full text | `2001.10721` | 1 document |
| 112 | 2026-11-09 | arXiv PDF full text | `1710.06829` | 1 document |
| 113 | 2026-11-09 | arXiv abs page | `2001.10721` | 1 record |
| 114 | 2026-11-09 | arXiv abs page | `1710.06829` | 1 record |
| 115 | 2026-11-09 | zbMATH Open API | `Patra Karttunen stencils isotropic discretization error` | 1 shown / 1 total |
| 116 | 2026-11-09 | zbMATH Open API | `LeVeque finite difference methods ordinary partial differential equations steady-state time-dependent` | 1 shown / 1 total |
| 117 | 2026-11-09 | zbMATH Open API | `Kumar isotropic finite-differences` | 2 shown / 2 total |
| 118 | 2026-11-09 | Crossref works/DOI | `10.1137/1.9780898717839` | 1 record |
| 119 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevA.77.062331` | 1 record |
| 120 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevA.69.052323` | 1 record |
| 121 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevLett.106.080502` | 1 record |
| 122 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevB.74.085308` | 1 record |
| 123 | 2026-11-09 | Crossref works/DOI | `10.1103/RevModPhys.81.109` | 1 record |
| 124 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevLett.53.2449` | 1 record |
| 125 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRev.71.622` | 1 record |
| 126 | 2026-11-09 | arXiv PDF full text | `cond-mat/0505308` | 1 document |
| 127 | 2026-11-09 | arXiv PDF full text | `0709.1163` | 1 document |
| 128 | 2026-11-09 | arXiv PDF full text | `1509.02295` | 1 document |
| 129 | 2026-11-09 | OpenAlex works/doi + APS abstract page | `10.1103/PhysRevLett.53.2449` | 1 record |
| 130 | 2026-11-09 | arXiv web search (title) | `Limit distributions of two-dimensional quantum walks` | 0 shown / 1 total (parser bug; re-run as #133-135) |
| 131 | 2026-11-09 | arXiv web search (title) | `Localization of two-dimensional quantum walks` | 0 shown / 7 total (parser bug; re-run as #133-135) |
| 132 | 2026-11-09 | arXiv web search (title) | `Mimicking the probability distribution of a two-dimensional Grover walk` | 0 shown / 1 total (parser bug; re-run as #133-135) |
| 133 | 2026-11-09 | arXiv web search (title) | `Limit distributions of two-dimensional quantum walks` | 1 shown / 1 total |
| 134 | 2026-11-09 | arXiv web search (title) | `Localization of two-dimensional quantum walks` | 7 shown / 7 total |
| 135 | 2026-11-09 | arXiv web search (title) | `Mimicking the probability distribution of a two-dimensional Grover walk` | 1 shown / 1 total |
| 136 | 2026-11-09 | arXiv PDF full text | `0802.2749` | 1 document |
| 137 | 2026-11-09 | arXiv PDF full text | `quant-ph/0311118` | 1 document |
| 138 | 2026-11-09 | arXiv PDF full text | `1010.2470` | 1 document |
| 139 | 2026-11-09 | arXiv web search (all) | `quantum walk dispersive estimate` | 2 shown / 2 total |
| 140 | 2026-11-09 | arXiv web search (all) | `quantum walk Strichartz` | 3 shown / 3 total |
| 141 | 2026-11-09 | arXiv web search (all) | `two-dimensional quantum walk decay estimate` | 1 shown / 1 total |
| 142 | 2026-11-09 | zbMATH Open API | `Maeda Sasaki Segawa Suzuki dispersive estimates quantum walks 1D lattice` | 1 shown / 1 total |
| 143 | 2026-11-09 | zbMATH Open API | `two-dimensional quantum walk weak limit theorem` | 4 shown / 4 total |
| 144 | 2026-11-09 | zbMATH Open API | `ti:quantum walk ti:two-dimensional` | 9 shown / 9 total |
| 145 | 2026-11-09 | arXiv web search (title) | `Two-dimensional quantum random walk` | 8 shown / 8 total |
| 146 | 2026-11-09 | arXiv web search (all) | `Pemantle quantum walk` | 2 shown / 2 total |
| 147 | 2026-11-09 | Crossref works/DOI | `10.1007/s10955-010-0098-2` | 1 record |
| 148 | 2026-11-09 | arXiv abs page | `0810.5495` | 1 record |
| 149 | 2026-11-09 | arXiv abs page | `0903.2967` | 1 record |
| 150 | 2026-11-09 | arXiv PDF full text | `0810.5495` | 1 document |
| 151 | 2026-11-09 | zbMATH Open API | `au:Ikromov au:Mueller` | 10 shown / 10 total |
| 152 | 2026-11-09 | zbMATH Open API | `Arnold normal forms of functions near degenerate critical points Weyl groups Lagrangian singularities` | 1 shown / 1 total |
| 153 | 2026-11-09 | zbMATH Open API | `Arnold remarks on the stationary phase method and Coxeter numbers` | 1 shown / 1 total |
| 154 | 2026-11-09 | zbMATH Open API | `Duistermaat oscillatory integrals Lagrange immersions unfolding of singularities` | 0 shown / 0 total |
| 155 | 2026-11-09 | zbMATH Open API | `Karpushkin theorem uniform estimates oscillatory integrals phase depending on two variables` | 1 shown / 1 total |
| 156 | 2026-11-09 | Crossref works/DOI | `10.1007/BF01075524` | 1 record |
| 157 | 2026-11-09 | Crossref works/DOI | `10.1515/9781400881246` | 1 record |
| 158 | 2026-11-09 | Crossref works/DOI | `10.1007/s11511-010-0047-6` | 1 record |
| 159 | 2026-11-09 | Crossref works/DOI | `10.1007/BF01077644` | 1 record |
| 160 | 2026-11-09 | Crossref works/DOI | `10.1070/rm1973v028n05ABEH001609` | 1 record |
| 161 | 2026-11-09 | Crossref works/DOI | `10.1002/cpa.3160270205` | 1 record |
| 162 | 2026-11-09 | zbMATH Open API | `an:0278.57011 (review text)` | 1 record |
| 163 | 2026-11-09 | zbMATH Open API | `an:0291.40005 (review text)` | 1 record |
| 164 | 2026-11-09 | zbMATH Open API | `an:0351.32011 (review text)` | 1 record |
| 165 | 2026-11-09 | zbMATH Open API | `an:0569.58033 (review text)` | 1 record |
| 166 | 2026-11-09 | Springer publisher page | `10.1007/BF01077644 (abstract)` | FAILED (HTTP 429) |
| 167 | 2026-11-09 | arXiv web search (all) | `van der Corput Lean` | 0 shown / 0 total |
| 168 | 2026-11-09 | arXiv web search (all) | `stationary phase formalization` | 50 shown / 195 total |
| 169 | 2026-11-09 | arXiv web search (all) | `oscillatory integral formalized proof assistant` | 0 shown / 0 total |
| 170 | 2026-11-09 | arXiv web search (all) | `Morse lemma formalization` | 4 shown / 4 total |
| 171 | 2026-11-09 | arXiv web search (all) | `Lean 4 harmonic analysis formalization` | 2 shown / 2 total |
| 172 | 2026-11-09 | arXiv web search (all) | `Isabelle Fourier analysis formalization` | 2 shown / 2 total |
| 173 | 2026-11-09 | arXiv web search (all) | `formalization Carleson theorem Lean` | 3 shown / 3 total |
| 174 | 2026-11-09 | arXiv PDF full text | `2405.06423` | 1 document |
| 175 | 2026-11-09 | arXiv PDF full text | `2609.31334` | 1 document |
| 176 | 2026-11-09 | arXiv abs page | `2405.06423` | 1 record |
| 177 | 2026-11-09 | arXiv abs page | `2609.31334` | 1 record |
| 178 | 2026-11-09 | GitHub code search API | `"stationary phase" language:Lean` | 42 total (repo list inspected) |
| 179 | 2026-11-09 | GitHub code search API | `"van der Corput" language:Lean` | 23 total (repo list inspected) |
| 180 | 2026-11-09 | GitHub code search API | `"Corput" language:Lean` | 45 total (repo list inspected) |
| 181 | 2026-11-09 | GitHub code search API | `"oscillatory integral" language:Lean` | 50 total (repo list inspected) |
| 182 | 2026-11-09 | GitHub code search API | `"Morse lemma" language:Lean` | 23 total (repo list inspected) |
| 183 | 2026-11-09 | GitHub code search API | `"Airy" "oscillatory" language:Lean` | 21 total (repo list inspected) |
| 184 | 2026-11-09 | GitHub code search API | `"van der Corput" language:Isabelle` | 0 total (repo list inspected) |
| 185 | 2026-11-09 | GitHub code search API | `"stationary phase" language:Coq` | 0 total (repo list inspected) |
| 186 | 2026-11-09 | GitHub repos API | `descriptions of 9 repos found by code search` | FAILED (HTTP 403); READMEs read via raw.githubusercontent.com instead |
| 187 | 2026-11-09 | raw.githubusercontent.com | `2 Lean files (lean-spherical OneDimStationaryPhase, lean-DLMF StationaryPhase) declarations grep` | 2 files |
| 188 | 2026-11-09 | Isabelle AFP entries index (isa-afp.org/entries) | `grep Corput\|stationary\|oscillat\|Morse\|Fourier\|Weyl\|exponential sum` | see report |
| 189 | 2026-11-09 | arXiv web search (title) | `Stencils with isotropic discretization error for differential operators` | 0 shown / 0 total |
| 190 | 2026-11-09 | arXiv web search (title) | `Isotropic finite-differences` | 3 shown / 3 total |
| 191 | 2026-11-09 | arXiv web search (all) | `nine-point compact Laplacian` | 0 shown / 0 total |
| 192 | 2026-11-09 | arXiv PDF full text | `2110.12448` | 1 document |
| 193 | 2026-11-09 | arXiv abs page | `2110.12448` | 1 record |
| 194 | 2026-11-09 | Crossref works/DOI | `10.1016/j.jcp.2022.111069` | 1 record |
| 195 | 2026-11-09 | arXiv PDF full text | `1901.05432` | 1 document |
| 196 | 2026-11-09 | arXiv PDF full text | `2310.15331` | 1 document |
| 197 | 2026-11-09 | arXiv PDF full text | `2006.14729` | 1 document |
| 198 | 2026-11-09 | arXiv web search (title) | `Robustness of the van Hove scenario for high-Tc superconductors` | 1 shown / 1 total |
| 199 | 2026-11-09 | arXiv web search (all) | `t-t' Hubbard model square lattice van Hove` | 17 shown / 17 total |
| 200 | 2026-11-09 | arXiv PDF full text | `cond-mat/0110516` | 1 document |
| 201 | 2026-11-09 | arXiv PDF full text | `1512.04271` | 1 document |
| 202 | 2026-11-09 | arXiv abs page | `cond-mat/0110516` | 1 record |
| 203 | 2026-11-09 | arXiv abs page | `1512.04271` | 1 record |
| 204 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevLett.89.076401` | 1 record |
| 205 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevB.94.085106` | 1 record |
| 206 | 2026-11-09 | Crossref works/DOI | `10.1007/978-3-319-25607-8` | 1 record |
| 207 | 2026-11-09 | Crossref works/DOI | `10.1016/j.cpc.2017.10.010` | 1 record |
| 208 | 2026-11-09 | arXiv web search (all) | `discrete Dirac equation dispersive estimate` | 3 shown / 3 total |
| 209 | 2026-11-09 | arXiv web search (all) | `honeycomb lattice dispersive estimate` | 6 shown / 6 total |
| 210 | 2026-11-09 | arXiv web search (all) | `triangular lattice dispersive estimate` | 6 shown / 6 total |
| 211 | 2026-11-09 | arXiv web search (all) | `lattice graph dispersive estimate oscillatory integral singularity` | 0 shown / 0 total |
| 212 | 2026-11-09 | arXiv web search (all) | `Kagome lattice dispersive estimate` | 4 shown / 4 total |
| 213 | 2026-11-09 | arXiv web search (all) | `periodic graph time decay estimate Schrodinger` | 0 shown / 0 total |
| 214 | 2026-11-09 | MathOverflow (StackExchange API search/advanced) | `lattice dispersive estimate` | n= 1 |
| 215 | 2026-11-09 | MathOverflow (StackExchange API search/advanced) | `discrete Schrodinger decay` | n= 6 |
| 216 | 2026-11-09 | MathOverflow (StackExchange API search/advanced) | `stationary phase degenerate torus` | n= 0 |
| 217 | 2026-11-09 | MathOverflow (StackExchange API search/advanced) | `van der Corput two dimensions` | n= 0 |
| 218 | 2026-11-09 | MathOverflow (StackExchange API search/advanced) | `caustic discrete Laplacian` | n= 0 |
| 219 | 2026-11-09 | MathOverflow (StackExchange API search/advanced) | `Lean stationary phase` | n= 0 |
| 220 | 2026-11-09 | zbMATH Open API | `an:1370.41055 (review text)` | 1 record |
| 221 | 2026-11-09 | zbMATH Open API | `an:1215.82025 (review text)` | 1 record |
| 222 | 2026-11-09 | zbMATH Open API | `Sunada Tate asymptotic behavior of quantum walks on the line` | 1 shown / 1 total |
| 223 | 2026-11-09 | arXiv web search (all) | `King's graph Schrodinger dispersive` | 0 shown / 0 total |
| 224 | 2026-11-09 | arXiv web search (all) | `Wan Zhang discrete Schrodinger` | 2 shown / 2 total |
| 225 | 2026-11-09 | arXiv web search (all) | `dispersive estimates discrete Schrodinger next-nearest neighbor` | 0 shown / 0 total |
| 226 | 2026-11-09 | arXiv web search (all) | `Grover walk two-dimensional time decay` | 0 shown / 0 total |
| 227 | 2026-11-09 | arXiv web search (all) | `Fermi surface caustics lattice Gauss map singularities` | 0 shown / 0 total |
| 228 | 2026-11-09 | arXiv PDF full text | `2507.20142` | 1 document |
| 229 | 2026-11-09 | Crossref query.bibliographic | `The wave equation on lattices and oscillatory integrals Bi Cheng Hua` | 5 shown / 1897903 total |
| 230 | 2026-11-09 | Crossref query.bibliographic | `Hong Tadano Yang dispersive estimates discrete Schrodinger honeycomb lattice` | 3 shown / 3639647 total |
| 231 | 2026-11-09 | Crossref works/DOI | `10.1016/j.aim.2026.111368` | 1 record |
| 232 | 2026-11-09 | arXiv web search (all) | `honeycomb lattice staggered sublattice potential tight-binding band gap` | 0 shown / 0 total |
| 233 | 2026-11-09 | arXiv web search (all) | `Semenoff mass honeycomb` | 4 shown / 4 total |
| 234 | 2026-11-09 | arXiv web search (all) | `hexagonal boron nitride tight-binding staggered potential` | 2 shown / 2 total |
| 235 | 2026-11-09 | arXiv web search (title) | `Haldane model honeycomb band structure` | 0 shown / 0 total |
| 236 | 2026-11-09 | zbMATH Open API | `an:0963.78001 (source field)` | 1 record |
| 237 | 2026-11-09 | zbMATH Open API | `an:1127.65080 (source field)` | 1 record |
| 238 | 2026-11-09 | zbMATH Open API | `an:1098.65108 (source field)` | 1 record |
| 239 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevResearch.4.013105` | 1 record |
| 240 | 2026-11-09 | Crossref works/DOI | `10.1103/PhysRevResearch.1.033135` | 1 record |
| 241 | 2026-11-09 | Crossref works/DOI | `10.1007/s00209-007-0125-4` | 1 record |
| 242 | 2026-11-09 | Crossref works/DOI | `10.2969/jmsj/85218521` | 1 record |
| 243 | 2026-11-09 | Crossref works/DOI | `10.1016/j.jfa.2011.12.016` | 1 record |
| 244 | 2026-11-09 | Crossref works/DOI | `10.1109/TAP.1966.1138693` | 1 record |


## 2. Task A: prior art, verified references

### A.1 Degenerate points / caustics of lattice dispersion relations and time decay

**[1] Cuenin, Jean-Claude; Ikromov, Isroil A.** "Sharp time decay estimates for the discrete Klein–Gordon equation". *Nonlinearity* 34(11), 7938–7962 (2021). DOI 10.1088/1361-6544/ac2b86. arXiv:2011.12076. [CR][arX]
- Model: u_tt − Δu + u = F on Z^d, with ω(ξ) = √(1 + Σ_j 2(1 − cos ξ_j)). That is, mass 1 only.
- Rates (Theorem 1): |t|^{-3/4} for d=2, |t|^{-7/6} for d=3, |t|^{-3/2} log|t| for d=4. They state the rates are sharp (Remark 1).
- **This is a census in your sense.** For each critical point x0 of Φ = ω(x) − s·x with s = ∇ω(x0), they classify the singularity type.
- **Proposition 9 (d=2):** only A_k with k ≤ 3 occur. A3 occurs iff cos x1 = cos x2 = 0, i.e. at the four points (±π/2, ±π/2). Otherwise the point is A1 or A2. A≥4 is excluded (Lemma 8).
- d=3: A_k (k ≤ 5) and D4−. d=4: additionally a T_{4,4,4}-like (hyperbolic) point.
- They also note that in d ≤ 4 the stable singularities are Thom's seven (A2–A5, D4±, D5).
- **Fully anticipates the census of M-f for m = 1.**

**[2] Borovyk, Vita; Goldberg, Michael.** "The Klein–Gordon equation on Z² and the quantum harmonic lattice". *J. Math. Pures Appl.* 107(6), 667–696 (2017). DOI 10.1016/j.matpur.2016.10.002. arXiv:1304.6353. [CR][arX]
- Model: γ²(k) = ω² + Σ_j 2λ_j(1 − cos k_j), for all ω, λ_j > 0. This covers every mass and anisotropic hopping.
- Global bound |t|^{-3/4}. The maxima occur near the four cusps of an astroid-shaped caustic curve, and there are four caustic lines inside the light cone.
- They state: "The fact that only fold and cusp singularities appear in this problem is noteworthy in itself", and that there is "no bifurcation of the number or type of caustics" for any parameters.
- They use Varchenko's Newton-polyhedron method and an Ikromov–Müller stability result.
- **Anticipates the M-f census for all m > 0, anisotropic case included.**

**[3] Schultz, Pete.** "The wave equation on the lattice in two and three dimensions". *Comm. Pure Appl. Math.* 51(6), 663–695 (1998). DOI 10.1002/(sici)1097-0312(199806)51:6<663::aid-cpa4>3.0.co;2-5. [CR] Crossref gives the author as "Pete Schultz". The text was NOT read.
- Content as reported by the citing papers I did read:
  - Borovyk–Goldberg: "exhibiting an explicit unfolding for each of the fold and cusp singularities that arise", plus an astroid-shaped secondary region.
  - Bi–Cheng–Hua: rates |t|^{-3/4} (d=2) and |t|^{-7/6} (d=3).
  - zbMATH review (Zbl 0928.35089): additional surfaces of concentration inside the light cone, pointwise and ℓ^p–ℓ^q estimates.
- For the massless case the phase also has an absolute-value (conical) singularity at k = 0 (Borovyk–Goldberg's wording).
- **Anticipates the census of the massless discrete wave equation on Z²: A1/A2/A3 plus a cone at the origin.**

**[4] Stefanov, Atanas; Kevrekidis, Panayotis G.** "Asymptotic behaviour of small solutions for the discrete nonlinear Schrödinger and Klein–Gordon equations". *Nonlinearity* 18(4), 1841–1857 (2005). DOI 10.1088/0951-7715/18/4/022. arXiv:nlin/0409009. [CR][arX] (The arXiv title spells it "behavior".)
- Discrete Schrödinger and Klein–Gordon on Z^d: decay ‖U(t)f‖_∞ ≤ C(1+|t|)^{-d/3}‖f‖_1. The Schrödinger case is proved by separation of variables and the 1D van der Corput lemma.
- In 2D this gives |t|^{-2/3} for Schrödinger. It is not sharp for Klein–Gordon, where [1] and [2] improve it to 3/4.
- No singularity classification.

**[5] Bi, Cheng; Cheng, Jiawei; Hua, Bobo.** "The Wave Equation on Lattices and Oscillatory Integrals". arXiv:2312.04130 (v3). [arX] I found no journal version: zbMATH lists only the arXiv record, and the Crossref search returned only [6].
- This is the "Bi, Cheng, Li?" of the brief: the third author is **Hua**.
- Main result: wave equation on Z⁴, sharp |t|^{-3/2} log|t|.
- Table 2 lists the d=2 normal forms with their decay exponents: ξ1³ (+ξ2²) → −5/6 (A2), and ξ1² + ξ1ξ2² → −3/4 (A3).
- They state that the stable singularities appearing in their proof are A_k and D4−.

**[6] Bi, Cheng; Cheng, Jiawei; Hua, Bobo.** "Sharp dispersive estimates for the wave equation on the five-dimensional lattice graph". *J. Evol. Equ.* 26(2), article 77 (2026). DOI 10.1007/s00028-026-01205-x. [CR] Rate |t|^{-11/6} on Z⁵ (from the arXiv:2406.00949 abstract).
- Also seen: You, Zhe; Zhan, Xiongfeng, arXiv:2609.05930 (wave equation on Z^d, d ≥ 5) [arX abstract]. Higher-dimensional, tangential.

**[7] Ge, Huabin; Hua, Bobo; Jia, Longsong; Zhou, Puchun.** "The asymptotic behavior of discrete Schrödinger equation on the hexagonal triangulation". *Calc. Var. Partial Differential Equations* 64(6), article 176 (2025). DOI 10.1007/s00526-025-03026-1. arXiv:2412.02947, whose arXiv title is "Asymptotic behavior of discrete Schrödinger equations on the hexagonal triangulation". [CR][arX]
- This is the triangular lattice (M-c). Rate ⟨t⟩^{-3/4}.
- Hessian corank ≤ 1 everywhere.
- Lemma 4.3: at every degenerate point the phase is either α20u1² + α12u1u2² + α04u2⁴ (R-nondegenerate, i.e. A3) or β20u1² + β03u2³ (A2).
- A≥4 is excluded by showing three curves do not intersect (their Prop. 6.1, appendix).
- **Anticipates the M-c census.**
- Related: Ge, Lu, Yu, "Discrete Four-Order Schrödinger Equation on the Hexagonal Triangulation", *J. Math. Study* 58(4), 439–458 (2025), DOI 10.4208/jms.v58n4.25.03 [CR]. Text not read.

**[8] Hong, Younghun; Tadano, Yukihide; Yang, Changhun.** "On the dispersive estimates for the discrete Schrödinger equation on a honeycomb lattice". *Adv. Math.* 507, 111368 (2026). DOI 10.1016/j.aim.2026.111368. arXiv:2503.08996. [CR][arX]
- Graphene nearest-neighbour model (M-h, gapless).
- Theorem 2.1: det ∇²φ = 3α1α2α12/(4φ⁴). So the degenerate set is the three curves α1 = 0, α2 = 0, α12 = 0, which meet only at the Dirac points.
- Frequency-localised rates (Theorem 2.3):
  - |t|^{-1} at nondegenerate points
  - |t|^{-5/6} on the curves (K1)
  - |t|^{-2/3} at pairwise curve intersections (K2)
  - |t|^{-5/6} at the Dirac points (K3, cones; optimality there not proven)
- Global rate |t|^{-2/3}.
- Own inference, not stated in the text as ADE labels: their Hessian formula vanishes identically when two α's vanish, so K2 points have corank 2. That fits D4 (D4 gives 2/3). The uniform 5/6 on K1 fits A2 only, i.e. no cusps.
- **Anticipates the census for gapless graphene**, including the non-smooth Dirac cones.

**[9] Wan, Zhiqiang; Zhang, Heng.** "Strichartz estimate for discrete Schrödinger equation on layered King's grid". arXiv:2507.20142. [arX] No journal version found; zbMATH lists only arXiv.
- The 3D layered grid factorises. The 2D factor is the **King's graph**: ω(x,y) = 8 − 2cos x − 2cos y − 2cos(x+y) − 2cos(x−y), their eq. (1.3).
- Their eq. (2.3) partitions the torus into Σ1 (det Hess ≠ 0), Σ2 (A2 points) and Σ3 (A3 points) of "ω(x,y) − (x,y)·∇_{(x0,y0)}ω". They state "the types of singularity are exactly A_k, k ≤ 3" (Prop. 2.3).
- **This is literally the census formulation of your project, for one model.** Own algebra: 2cos(x+y) + 2cos(x−y) = 4cos x cos y, so the King's graph is the t–t′ model M-b with t′ = t.

**[10] Cheng, Jiawei.** "The fourth-order Schrödinger equation on lattices". arXiv:2403.07445 [arX]. i∂_t u + Δ²u − γΔu on Z^d, d = 1, 2. The 2D phase is analysed by Newton polyhedra, with case-by-case exponents −3/4, −5/6, −1/2 (log) in its Section 3. Follow-up: Cheng, arXiv:2609.37300, sharp |t|^{-d/4} [arX abstract].

**[11] Cuenin, Jean-Claude; Schippa, Robert.** "Fourier transform of surface–carried measures of two-dimensional generic surfaces and applications". *Commun. Pure Appl. Anal.* 21(9), 2873– (2022). Crossref gives first page 2873 only; zbMATH gives pp. 2873–2889. DOI 10.3934/cpaa.2022079. [CR][arX]
- Generic surfaces: the Gauss map has only folds (A2) and cusps (A3), following Whitney. Decay λ^{-1/2-1/k}.
- Applied to the discrete Schrödinger operator on Z³.
- Its text attributes earlier work to **Erdős, László; Salmhofer, Manfred**, "Decay of the Fourier transform of surfaces with vanishing curvature", *Math. Z.* 257(2), 261–294 (2007), DOI 10.1007/s00209-007-0125-4 [CR]. That paper concerns lattice Fermi surfaces in 3D; I did not read it.

**Other verified, more tangential works:**
- Hong, Younghun; Yang, Changhun, "Uniform Strichartz estimates on the lattice", *Discrete Contin. Dyn. Syst.* 39(6), 3239–3264 (2019), DOI 10.3934/dcds.2019134 [CR].
- Kassem, Sagiv, Weinstein, arXiv:2605.08372 (1D SSH model) [arX abstract].
- Kopylova, arXiv:0812.0468 (discrete 3D) — zbMATH hit only, not opened.

**Answer for item 1.** In 2D the following censuses already exist in the literature:
- square-lattice Klein–Gordon (all masses)
- square-lattice wave equation
- triangular-lattice Schrödinger
- King's-graph Schrödinger
- gapless honeycomb Schrödinger

The singularity types found are:
- A1, A2 and A3 for Klein–Gordon, the wave equation, the triangular lattice and the King's graph; A3 is always at isolated points and A≥4 is excluded.
- A cone at k = 0 for the massless wave equation.
- Folds, corank-2 points (rate 2/3) and Dirac cones for graphene.

### A.2 Catastrophe / ADE classification of band-structure critical points

**[12] Chandrasekaran, Anirudh; Shtyk, Alex; Betouras, Joseph J.; Chamon, Claudio.** "Catastrophe theory classification of Fermi surface topological transitions in two dimensions". *Phys. Rev. Research* 2(1), 013355 (2020). DOI 10.1103/physrevresearch.2.013355. arXiv:1910.10183. [CR][arX]
- Classifies singularities of the dispersion ε(k) at Fermi-surface topological transitions: 17 catastrophe types for ≤ 7 control parameters.
- Gives density-of-states exponents and wallpaper-group constraints at high-symmetry points.
- These are **critical points of ε itself (∇ε = 0)**, i.e. singularities of the level-set family. They are not caustics of the gradient map. "Caustics" appears only in their references.

**[13] Yuan, Noah F. Q.; Isobe, Hiroki; Fu, Liang.** "Magic of high-order van Hove singularity". *Nature Communications* 10(1), 5769 (2019). DOI 10.1038/s41467-019-13670-9. arXiv:1901.05432; the arXiv title has "high order" without the hyphen. [CR][arX] Higher-order saddle points of the band (∇ε = 0). Not caustics.

**[14] Chandrasekaran, Anirudh; Betouras, Joseph J.** "A Practical Method to Detect, Analyze, and Engineer Higher Order Van Hove Singularities in Multi-band Hamiltonians". *Advanced Physics Research* 2(5), 2200061 (2023). DOI 10.1002/apxr.202200061. [CR][arX] Taylor expansion of bands at arbitrary k via a generalised Feynman–Hellmann theorem. Still ∇ε = 0.

**[15] Kirkby, W.; Mumford, J.; O'Dell, D. H. J.** "Quantum caustics and the hierarchy of light cones in quenched spin chains". *Phys. Rev. Research* 1(3), 033135 (2019). DOI 10.1103/physrevresearch.1.033135 [CR][arX abstract]
- Lattice light cones treated as caustics of the propagator (fold/Airy, cusp/Pearcey, hyperbolic umbilic for multisite correlators).
- Models: **1D** transverse-field Ising and XY chains.

**[16] Kirkby, W.; Yee, Y.; Shi, K.; O'Dell, D. H. J.** "Caustics in quantum many-body dynamics". *Phys. Rev. Research* 4(1), 013105 (2022). DOI 10.1103/physrevresearch.4.013105 [CR][arX abstract]
- Fock-space caustics of the Bose–Hubbard dimer and trimer.
- The abstract calls the hyperbolic and elliptic umbilics (D4±) "codimension-3".
- Also seen: Roy, Mumford, O'Dell, Dalla Torre, arXiv:2410.06803 (1D transverse-field Ising caustic scaling) [arX abstract].

**Answer for item 2.** The band-structure ADE works [12–14] classify ∇ε = 0 points, not caustics of k ↦ ∇ε(k). The physics caustic works [15–16] are 1D chains or Fock space.

In this sweep, the only works that classify **every point k0 of the 2D torus for ε(k) − ∇ε(k0)·k** are the dispersive-estimate papers of A.1. Each treats one model:
- [1, 2] square-lattice Klein–Gordon
- [3, 5] square-lattice wave equation
- [7] triangular lattice
- [8] honeycomb lattice
- [9] King's graph

I found no work that does this census across several standard models, or for the t–t′ model with general t′/t, the 9-point stencil, Yee, Qi–Wu–Zhang, gapped graphene or 2D quantum walks.

### A.3 Dispersive properties of numerical schemes

**[17] Ignat, Liviu I.; Zuazua, Enrique.** "Numerical Dispersive Schemes for the Nonlinear Schrödinger Equation". *SIAM J. Numer. Anal.* 47(2), 1366–1390 (2009). DOI 10.1137/070683787. [CR; abstract read from Crossref]
- The conservative finite-difference semidiscretisation "lose[s] the dispersion property" uniformly in h.
- They prove this by concentrating solutions "at the points of the spectrum where the second order derivatives of the symbol of the discrete Laplacian vanish".
- Remedies: Fourier filtering and a two-grid preconditioner.
- It identifies degenerate points of the symbol. It does not classify their singularity type in 2D.

**Other verified works on numerical schemes:**
- **[18]** Ignat, Liviu I.; Zuazua, Enrique, "Convergence rates for dispersive approximation schemes to nonlinear Schrödinger equations", *J. Math. Pures Appl.* 98(5), 479–517 (2012), DOI 10.1016/j.matpur.2012.01.001 [CR].
  - Also [zb]: Ignat–Zuazua, *C. R. Math. Acad. Sci. Paris* 340, 529–534 (2005), DOI 10.1016/j.crma.2005.02.024 (viscous scheme); and ibid. 341, 381–386 (2005), DOI 10.1016/j.crma.2005.07.018 (two-grid).
- **[19]** Zuazua, Enrique, "Propagation, Observation, and Control of Waves Approximated by Finite Difference Methods", *SIAM Review* 47(2), 197–243 (2005), DOI 10.1137/s0036144503432862 [CR].
- **[20]** Trefethen, Lloyd N., "Group Velocity in Finite Difference Schemes", *SIAM Review* 24(2), 113–136 (1982), DOI 10.1137/1024038 [CR].
  - Also [zb]: Vichnevetsky, R., "Group velocity and reflection phenomena in numerical approximations of hyperbolic equations", *J. Franklin Inst.* 315, 307–330 (1983), DOI 10.1016/0016-0032(83)90056-X.
- **[21]** David, Cl.; Sagaut, P.; Sengupta, T., "A linear dispersive mechanism for numerical error growth: spurious caustics", *European Journal of Mechanics – B/Fluids* 28(1), 146–151 (2009), DOI 10.1016/j.euromechflu.2008.04.002 [CR].
  - **Content NOT VERIFIED.** The abstract was unavailable (Crossref and OpenAlex have none, ScienceDirect returned 403, and the zbMATH text is withheld). The title shows that caustics of numerical dispersion relations have been studied. I could not determine the dimension or whether a classification is given.
  - Related [zb]: Sengupta et al., *Appl. Math. Comput.* 218, 9035–9065 (2012), DOI 10.1016/j.amc.2012.03.030.
- No paper found that classifies caustics (A2/A3/D4) of the 2D Yee/FDTD numerical dispersion relation, or proves ℓ¹→ℓ∞ decay rates for Yee.

### A.4 Quantum walks in 2D

**[22] Watabe, Kyohei; Kobayashi, Naoki; Katori, Makoto; Konno, Norio.** "Limit distributions of two-dimensional quantum walks". *Phys. Rev. A* 77(6), 062331 (2008). DOI 10.1103/physreva.77.062331. arXiv:0802.2749. [CR][arX] Weak limit theorems for a one-parameter generalized Grover family. Dispersion relation in B-i below.

**[23] Inui, Norio; Konishi, Yoshinao; Konno, Norio.** "Localization of two-dimensional quantum walks". *Phys. Rev. A* 69(5), 052323 (2004). DOI 10.1103/physreva.69.052323. arXiv:quant-ph/0311118. [CR][arX]
- **Discrepancy:** the brief says "Inui–Konishi–Segawa". The record's third author is **Norio Konno**.

**[24] Di Franco, C.; Mc Gettrick, M.; Busch, Th.** "Mimicking the Probability Distribution of a Two-Dimensional Grover Walk with a Single-Qubit Coin". *Phys. Rev. Lett.* 106(8), 080502 (2011). DOI 10.1103/physrevlett.106.080502. arXiv:1010.2470, which lists "M. McGettrick". [CR][arX] The text proves an amplitude correspondence. **It states no dispersion relation.**

**[25] Maeda, Masaya; Sasaki, Hironobu; Segawa, Etsuo; Suzuki, Akito; Suzuki, Kanako.** "Dispersive estimates for quantum walks on 1D lattice". *J. Math. Soc. Japan* 74(1), 217–246 (2022). DOI 10.2969/jmsj/85218521. arXiv:1808.05714. [CR][arX abstract] 1D, (1+|t|)^{-1/3}, with position-dependent coin.
- Also [zb]: Aso, Takumi; Maeda, Masaya, *Yokohama Math. J.* 67, 1–8 (2021), DOI 10.18880/00014917 (1D uniform Strichartz).

**[26] Baryshnikov, Yuliy; Brady, Wil; Bressler, Andrew; Pemantle, Robin.** "Two-dimensional Quantum Random Walk". *J. Stat. Phys.* 142(1), 78–107. Crossref issued date 2010-12-08; zbMATH and volume year 2011. DOI 10.1007/s10955-010-0098-2. arXiv:0810.5495. [CR][arX]
- The probability profile is "essentially a negative power of the Gaussian curvature" of an algebraic variety.
- The limit shape is the image of the logarithmic Gauss map. Curves where the curvature vanishes are discussed.
- This is the closest prior work on caustic geometry of 2D walks. It is not a decay-rate classification by ADE type, as far as I read.
- Follow-up: Bressler, Greenwood, Pemantle, Petkovšek, arXiv:0903.2967 [arX abstract].

**Other quantum-walk records:**
- Sunada, Toshikazu; Tate, Tatsuya, "Asymptotic behavior of quantum walks on the line", *J. Funct. Anal.* 262(6), 2608–2645 (2012), DOI 10.1016/j.jfa.2011.12.016 [CR] (1D).
- [zb]:
  - Tate, "Quantum walks in low dimension", Trends Math. (2016) 261–278, DOI 10.1007/978-3-319-31756-4_21 (text unavailable)
  - Asahara–Funakawa–Seki–Suzuki, arXiv:2408.09578 (2D quantum CLT)
  - Fuda–Funakawa–Sasayama–Suzuki, *Quantum Stud. Math. Found.* 10, 483–496 (2023), DOI 10.1007/s40509-023-00307-2 (2D split-step walk spectral theory)

**Answer for item 4.** No ℓ¹→ℓ∞ dispersive (decay-rate) estimate for any 2D quantum walk was found, and no singularity census of a 2D walk's quasi-energy.

### A.5 Newton polyhedra and normal forms

**Ikromov–Müller and related harmonic analysis:**
- **[27]** Ikromov, Isroil A.; Müller, Detlef, *Fourier Restriction for Hypersurfaces in Three Dimensions and Newton Polyhedra (AM-194)*. Princeton University Press, 2016. DOI 10.1515/9781400881246. [CR] Crossref types it as "edited-book". zbMATH: Annals of Mathematics Studies 194, viii+258 pp., Zbl 1352.42001.
- **[28]** Ikromov, Isroil A.; Kempe, Michael; Müller, Detlef, "Estimates for maximal functions associated with hypersurfaces in ℝ³ and related problems of harmonic analysis", *Acta Math.* 204(2), 151–271 (2010), DOI 10.1007/s11511-010-0047-6 [CR].
  - **Note:** the Acta paper is Ikromov–**Kempe**–Müller.
  - Also [zb]: Ikromov–Müller, "On adapted coordinate systems", *Trans. AMS* 363, 2821–2848 (2011), DOI 10.1090/S0002-9947-2011-04951-2.
  - Also [zb]: Ikromov–Müller, "Uniform estimates for the Fourier transform of surface carried measures in ℝ³ and an application to Fourier restriction", *J. Fourier Anal. Appl.* 17, 1292–1332 (2011), DOI 10.1007/s00041-011-9191-4. This is the linear-perturbation stability result used by [2].

**Singularity theory and oscillatory integrals:**
- **[29]** Varchenko, A. N., "Newton polyhedra and estimation of oscillating integrals", *Functional Analysis and Its Applications* 10(3), 175–196. DOI 10.1007/bf01075524. [CR]
  - Crossref issued date: 1976-07.
  - zbMATH (Zbl 0351.32011) lists year 1977, as a translation from *Funkts. Anal. Prilozh.* 10(3), 13–38 (1976).
- **[30]** Arnol'd, V. I., "Normal forms for functions near degenerate critical points, the Weyl groups of A_k, D_k, E_k and Lagrangian singularities", *Functional Analysis and Its Applications* 6(4), 254–272. DOI 10.1007/bf01077644. [CR]
  - Crossref issued date: 1972-10. zbMATH (Zbl 0278.57011) lists 1973.
- **[31]** Arnol'd, V. I., "Remarks on the stationary phase method and Coxeter numbers", *Russian Math. Surveys* 28(5), 19–48 (1973), DOI 10.1070/rm1973v028n05abeh001609 [CR].
- **[32]** Duistermaat, J. J., "Oscillatory integrals, lagrange immersions and unfolding of singularities", *Comm. Pure Appl. Math.* 27(2), 207–281 (1974), DOI 10.1002/cpa.3160270205 [CR].
- [zb]:
  - Karpushkin, V. N., "A theorem concerning uniform estimates of oscillating integrals with the phase depending on two variables", *Trudy Sem. Petrovsk.* 10, 150–169 (1984), Zbl 0569.58033, no DOI. This is the 2-variable uniform-estimate theorem used by [7], [9] and [5].
  - Arnold, Gusein-Zade, Varchenko, *Singularities of differentiable maps, Vol. 2*, Modern Birkhäuser Classics (2012), DOI 10.1007/978-0-8176-8343-6.

**Correction to the brief.** The brief says "Lagrangian singularities stable in 2D are A2, A3, D4±". I could not verify this, and the sources I read point the other way:
- [11] states that for 2-parameter families (Gauss maps of surfaces) "A1, A2, A3 singularities are the only generic ones", following Whitney.
- [16]'s abstract calls D4± "codimension-3".
- [1] lists Thom's seven for up to 4 parameters.

So D4± are generic in 3-parameter families, i.e. caustics in 3-space, not in the plane. In 2D lattice models, D4 points appear only through symmetry: graphene's K2 points [8] and, by my own derivation, the square-lattice Schrödinger model. Arnold's original text was not accessed (Springer returned 429), so the exact statement there is NOT VERIFIED.

### A.6 Formalisations

These are code-search results, not peer-reviewed records.

**GitHub code search:**
- `"stationary phase" language:Lean`: 42 hits. Relevant repositories:
  - roos-j/lean-spherical, file `LeanSpherical/Auto/OneDimStationaryPhase.lean`. It contains proved theorems such as `quadraticStationaryPhase` and `quadraticNormalFormStationaryPhase`: **1D quadratic (Morse) stationary phase**. The README says it is part of a spherical-maximal-function formalisation and that machine-generated code lives in `Auto`.
  - bjbraams/lean-DLMF, file `DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean`. Its theorems `stationaryPhase_watson` and `stationaryPhase_endpoint` end in `sorry`.
- `"van der Corput" language:Lean`: 23 hits; `"Corput"`: 45 hits.
  - fpvandoorn/carleson. The Carleson blueprint (arXiv:2405.06423, Lemma 11.1.7 "van der Corput") is a **linear-phase** bound |∫g e^{inx}| ≤ 2π|β−α|‖g‖_Lip(1+|n||β−α|)^{-1}. It is not the classical φ^{(k)} van der Corput.
  - roos-j repositories (lean-dfr, lean-discretesw: discrete Stein–Wainger Carleson operator, per its README).
  - Others not opened.
- `"oscillatory integral" language:Lean`: 50 hits. `"Morse lemma" language:Lean`: 23 hits; repositories were listed but not opened.
- Mathlib4 has **0** hits for "Corput" and **0** for "Morse lemma".
- Isabelle: 0 hits for `"van der Corput"`. Coq: 0 hits for `"stationary phase"`.
- Isabelle AFP index (1052 entry links): none on van der Corput, stationary phase, oscillatory integrals or the Morse lemma. The Fourier-related entries are Fourier Series, FFT, Budan–Fourier and Quantum Fourier Transform.

**arXiv:**
- Becker, de Frutos-Fernández, et al., "Formalizing Carleson's Theorem in Lean", arXiv:2609.31334 [arX abstract]
- Blueprint: arXiv:2405.06423 [arX]
- No paper on formalising 2D degenerate stationary phase, Newton-polyhedron bounds, or ADE classification was found.

**Answer for item 6.** There are Lean formalisations of 1D Morse stationary phase and of linear-phase van der Corput. I found **no formalisation of 2D degenerate oscillatory-integral bounds (A2/A3/D4), Varchenko/Karpushkin-type theorems, or singularity classification.** The caveat is that GitHub code search covers indexed default branches only.

## 3. Task B: dispersion relations as the sources state them

**M-a: square-lattice nearest-neighbour / discrete Laplacian.**
- Source: Stefanov–Kevrekidis [4] (arXiv text). Δ_d f = Σ_j (e^{2πik_j} + e^{−2πik_j} − 2) f = −4 Σ_j sin²(πk_j) f̂(k), with Fourier variable k ∈ [0,1]^d and lattice spacing h = 1.
- Hence the symbol is Σ_j (2cos 2πk_j − 2). This agrees with ε ∝ cos k1 + cos k2 up to the rescaling k ↦ 2πk and an affine shift. No discrepancy.
- Rate |t|^{-2/3} in 2D. Also stated by [2]: "separation of variables leads to a |t|^{-2/3} bound".
- Singularity labels: no source found that gives ADE labels for this model. **(Own derivation, not from a source):**
  - for the phase cos k1 + cos k2 − v·k, the Hessian is diag(−cos k1, −cos k2)
  - A2 on the lines cos k1 = 0 or cos k2 = 0 (excluding their intersections)
  - corank 2 at the four points (±π/2, ±π/2), with cubic ±η1³/6 ± η2³/6, which is a nondegenerate binary cubic, i.e. **D4**
  - no A3
  - If correct, M-a lies inside OscInt's current hypotheses (A1, A2, finitely many D4).

**M-b: t–t′ model.**
- Source: Irkhin, Katanin, Katsnelson, "Robustness of the Van Hove Scenario for High-T_c Superconductors", *Phys. Rev. Lett.* 89(7), 076401 (2002), DOI 10.1103/physrevlett.89.076401 [CR][arX cond-mat/0110516]. Eq. (2): **ε_k = −2t(cos k_x + cos k_y) − 4t′(cos k_x cos k_y + 1) − μ.**
  - It differs from the brief only by the constant −4t′ − μ, which does not affect the census.
- Sign conventions vary. Šimkovic, Liu, Deng, Kozik, *Phys. Rev. B* 94(8), 085106 (2016), DOI 10.1103/physrevb.94.085106 [CR][arX 1512.04271], eq. (2): ε(k) = −2t(cos k_x + cos k_y) **+ 4t′** cos k_x cos k_y.
- Prior census exists only at t′ = t (King's graph, [9]); see the own-algebra note there.

**M-c: triangular lattice.**
- Source: Ge–Hua–Jia–Zhou [7], eq. (1.5): **g(x) = 6 − 2cos x1 − 2cos x2 − 2cos(x1 + x2)**, x ∈ [0, 2π]².
- Convention: the graph is treated as "a Cayley graph of the two-dimensional lattice Z²", and the Fourier variable is dual to those Z² coordinates. From the formula, the generators are presumably ±e1, ±e2, ±(e1 + e2); this is my inference.
- It agrees with the brief's cos k1 + cos k2 + cos(k1 + k2) up to the affine map −2(·) + 6. No discrepancy.
- Hessian (4.1): 2[[cos(x1+x2) + cos x1, cos(x1+x2)], [cos(x1+x2), cos(x1+x2) + cos x2]].

**M-d: 9-point isotropic Laplacian.**
- Source: Ji, Kaihua; Tabrizi, Amirhossein Molavi; Karma, Alain, "Isotropic finite-difference approximations for phase-field simulations of polycrystalline alloy solidification", *J. Comput. Phys.* 457, 111069 (2022), DOI 10.1016/j.jcp.2022.111069 [CR][arX 2110.12448].
  - Eq. (25): L_{2,1} = (2/3)L_{1,0} + (1/3)L_{0,1} = **(1/(6h²))[4 Σ_{i=1}^4 ψ^i_⟨10⟩ + Σ_{i=1}^4 ψ^i_⟨01⟩ − 20ψ(0,0)]**.
  - Eq. (35): symbol −k² + k⁴/12 + O(k⁶), with isotropic leading error.
  - This matches the brief exactly.
- This is a computational-physics source, not a numerical-analysis monograph. LeVeque, *Finite Difference Methods for Ordinary and Partial Differential Equations*, SIAM 2007, DOI 10.1137/1.9780898717839 [CR], and Patra, Michael; Karttunen, Mikko, *Numer. Methods Partial Differ. Equ.* 22(4), 936–953 (2006), DOI 10.1002/num.20129 [zb] exist. Their texts were not accessed, so the stencil is **NOT VERIFIED against them**.
- **(Own derivation)** The Fourier symbol is (1/(6h²))[8(cos θ1 + cos θ2) + 4cos θ1 cos θ2 − 20]. This is the M-b form with **t′/t = 1/4**, up to an affine rescaling.

**M-e: 2D Yee/FDTD.**
- **Taflove & Hagness: NOT VERIFIED.** The book text was not accessed. zbMATH Zbl 0963.78001: Taflove, Allen; Hagness, Susan C., *Computational electrodynamics: the finite-difference time-domain method*, London: Artech House, xxiii+852 pp. with CD-ROM (2000), 2nd edition record. The 3rd edition (2005) is cited by the source below.
- Secondary verification: Cheng, Yu; Chen, Guangzhi; Wang, Xiang-Hua; Yang, Shunchuan, arXiv:2001.10721 [arX], which cites Taflove–Hagness 2005 as its [30].
  - Eq. (2), 3D, uniform medium: (sin(ωΔt/2)/(cΔt))² = Σ_{ξ=x,y,z} (sin(k̃_ξΔξ/2)/Δξ)².
  - Eq. (3): Δt ≤ √(εμ)/√((Δx)^{-2} + (Δy)^{-2} + (Δz)^{-2}).
- Also Blinne et al., "A systematic approach to numerical dispersion in Maxwell solvers", *Comput. Phys. Commun.* 224, 273–281 (2018), DOI 10.1016/j.cpc.2017.10.010 [CR][arX]. Eqs. (12)–(13) with all A = 1 reduce to the Yee relation, which they call "the well-known Yee dispersion".
- Dropping z gives exactly the brief's 2D formula and the 2D limit cΔt ≤ 1/√(1/Δx² + 1/Δy²). This step is my inference, not a quoted 2D statement. It is consistent with Schneider, *Understanding the FDTD Method* (author's PDF), which gives the 2D uniform-grid Courant limit 1/√2 and only the 1D dispersion relation (7.34).
- Primary scheme: Yee, Kane, "Numerical solution of initial boundary value problems involving maxwell's equations in isotropic media", *IEEE Trans. Antennas Propag.* 14(3), 302–307 (1966), DOI 10.1109/tap.1966.1138693 [CR]. Text not read.
- **(Own derivation)** With ν_x = cΔt/Δx and ν_y = cΔt/Δy: cos(ωΔt) = 1 − ν_x² − ν_y² + ν_x² cos(k_xΔx) + ν_y² cos(k_yΔy). At the 2D Courant limit (ν_x² + ν_y² = 1) this becomes **cos(ωΔt) = ν_x² cos θ1 + ν_y² cos θ2**, which is the M-i/M-j family below. Where the right-hand side reaches ±1 (θ = 0, or (π, π) at the limit), ω has **conical** points.

**M-f: discrete Klein–Gordon.**
- Cuenin–Ikromov [1]: u_tt − Δ_x u + u = F, with Δ_x u = Σ_{|x−y|=1} u(y) − 2d u(x). Hence ω(ξ) = √(1 + Σ_{j=1}^d 2(1 − cos ξ_j)), also written ω² = 1 + Σ sin²-type terms. Torus [0, 2π]^d.
  - In d = 2: ω² = 5 − 2cos ξ1 − 2cos ξ2. This is the brief's formula with **m = 1 only**; their mass is fixed at 1.
- Borovyk–Goldberg [2]: γ²(k) = ω² + Σ_j 2λ_j(1 − cos k_j), k ∈ [−π, π]². Here **ω denotes the mass**. This equals the brief's formula with λ1 = λ2 = 1 and their ω = m.

**M-g: Qi–Wu–Zhang.**
- Original: Qi, Xiao-Liang; Wu, Yong-Shi; Zhang, Shou-Cheng, "Topological quantization of the spin Hall effect in two-dimensional paramagnetic semiconductors", *Phys. Rev. B* 74(8), 085308 (2006), DOI 10.1103/physrevb.74.085308 [CR]. Read in arXiv:cond-mat/0505308 v4 (31 Aug 2006). The published PRB text was not read.
  - Eq. (1): H(k) = ε(k) + V d_α(k)σ^α, with E± = ε(k) ± V d(k).
  - Eq. (7) example: **d_x = sin k_y, d_y = −sin k_x, d_z = c(2 − cos k_x − cos k_y − e_s).**
- The brief's form appears verbatim as eq. (6.1) of Asbóth, János K.; Oroszlány, László; Pályi, András, *A Short Course on Topological Insulators*, Lecture Notes in Physics, Springer 2016, DOI 10.1007/978-3-319-25607-8 [CR][arX 1509.02295]:
  - Ĥ(k) = sin k_x σ̂_x + sin k_y σ̂_y + [u + cos k_x + cos k_y]σ̂_z
  - E± = ±√(sin²k_x + sin²k_y + (u + cos k_x + cos k_y)²), eq. (6.4)
  - They cite Qi–Wu–Zhang as their [24] for this model. They obtain it from a Rice–Mele pump by dimensional extension plus a unitary rotation; they do not compare it with the original's d-vector.
- **Discrepancies with the brief:**
  - (i) σ-labelling and sign: (sin k_y, −sin k_x) versus (sin k_x, sin k_y). Unitary, same spectrum.
  - (ii) The original has a scale c on d_z. With c = 1, d_z = −(m + cos k_x + cos k_y) with m = e_s − 2, giving the same |d|. For c ≠ 1 the original is a one-parameter generalisation.
  - (iii) The original has an ε(k) term, usually set to 0.
- Only |d(k)| and ε(k) enter the census.

**M-h: graphene.**
- Source: Castro Neto, A. H.; Guinea, F.; Peres, N. M. R.; Novoselov, K. S.; Geim, A. K., "The electronic properties of graphene", *Rev. Mod. Phys.* 81(1), 109–162 (2009), DOI 10.1103/revmodphys.81.109 [CR], read in arXiv:0709.1163.
  - Eq. (6): **E±(k) = ±t√(3 + f(k)) − t′f(k), f(k) = 2cos(√3 k_y a) + 4cos((√3/2)k_y a)cos((3/2)k_x a)**, attributed to Wallace (1947).
  - Eq. (1): a1 = (a/2)(3, √3), a2 = (a/2)(3, −√3), with a ≈ 1.42 Å the C–C distance.
- **(Own algebra)** 3 + f(k) = 3 + 2cos(k·a1) + 2cos(k·a2) + 2cos(k·(a1 − a2)). This matches the brief at t′ = 0.
- Hong–Tadano–Yang [8], eq. (2.1), use the same expression with v1 = (√3/2, 1/2) and v2 = (√3/2, −1/2), i.e. unit lattice constant.
- Wallace, P. R., "The Band Theory of Graphite", *Phys. Rev.* 71(9), 622–634 (1947), DOI 10.1103/physrev.71.622 [CR]. Text not read.
- **Gapped version:** Semenoff, Gordon W., "Condensed-Matter Simulation of a Three-Dimensional Anomaly", *Phys. Rev. Lett.* 53(26), 2449–2452 (1984), DOI 10.1103/physrevlett.53.2449 [CR]. Only the abstract was read.
  - **The formula E = ±√(Δ² + t²|f|²) is NOT VERIFIED from a source.** It is the immediate spectrum of [[Δ, −tf], [−tf*, −Δ]], which is my algebra.
  - The Castro Neto text I searched cites Semenoff only for the continuum Dirac Hamiltonian.

**M-i: Grover walk on Z².**
- Watabe et al. [22], eqs. (5)–(7): generalized Grover coin with parameter p ∈ (0,1), q = 1 − p; p = 1/2 gives the Grover coin. Eigenvalues **λ1 = 1, λ2 = −1, λ3,4 = e^{±iω(k_x,k_y)}, with cos ω(k_x, k_y) = −(p cos k_x + q cos k_y)**.
  - For Grover: **cos ω = −(cos k_x + cos k_y)/2**, with flat bands at ±1.
- Inui–Konishi–Konno [23], eqs. (11)–(14), on a finite N-torus with ξ_j = 2jπ/N: λ = −1, 1, [−cos ξ_m − cos ξ_n ∓ √(−4 + (cos ξ_m + cos ξ_n)²)]/2. Hence Re λ = −(cos ξ_m + cos ξ_n)/2, consistent with [22].
- **Discrepancy with the brief: the sign.** The brief's +(cos k1 + cos k2)/2 corresponds to k ↦ k + (π, π); this equivalence is my remark. Flat bands ±1: confirmed.

**M-j: cos ω = a cos k1 + b cos k2.**
- Verified instance: Watabe et al.'s generalized Grover family, cos ω = −(p cos k_x + q cos k_y) with p + q = 1 [22].
- Di Franco–Mc Gettrick–Busch [24]: **no dispersion relation is stated** in the text. For their alternate (single-qubit-coin) walk the relation is NOT FOUND / NOT VERIFIED.
- No other source with a ≠ b and a + b ≠ 1 was verified.
- **(Own derivation)** M-e at the Courant limit belongs to the same family, with a = ν_x², b = ν_y² and a + b = 1. At k = 0 and k = (π, π), where |a cos k1 + b cos k2| = 1, ω has conical points, e.g. ω ≈ π − √(p k_x² + q k_y²) for the walk at k = 0. These are non-smooth points like Dirac cones.

## 4. Novelty assessment (candid)

- **The census method (classify every torus point for ω(k) − ∇ω(k0)·k, then read off rates): PLAUSIBLE-not-novel.** It is anticipated, model by model, by:
  - Schultz 1998 [3] (square wave)
  - Borovyk–Goldberg [2] and Cuenin–Ikromov [1] (square Klein–Gordon)
  - Bi–Cheng–Hua [5] (square wave, with explicit normal-form table)
  - Ge–Hua–Jia–Zhou [7] (triangular)
  - Hong–Tadano–Yang [8] (gapless honeycomb)
  - Wan–Zhang [9] (King's graph, using the exact "ω − (x,y)·∇ω(x0,y0)" partition into A1/A2/A3)
- **Per-model status of the brief's list:**
  - M-a: rate known [4]; ADE labels not found in a source.
  - M-b: anticipated only at t′/t = 1 [9]. General t′/t: no anticipation found.
  - M-c: anticipated [7].
  - M-d: no anticipation found.
  - M-e: no anticipation found. "Spurious caustics" [21] exists but was unread.
  - M-f: anticipated [1, 2].
  - M-g: no anticipation found.
  - M-h gapless: anticipated [8]. Gapped (Semenoff): no anticipation found.
  - M-i/M-j: no decay-rate census found. Caustic geometry of 2D walks is partially anticipated by [26] (curvature / Gauss map).
- **A unified, exact, cross-model census** of these standard 2D dispersion relations was not found in this sweep. That gap is not proof of novelty: Google Scholar was unreachable, Crossref search was mostly rate-limited, and I did not read paywalled physics and numerical-analysis texts ([21] in particular). Wording to use: "no anticipation found in a logged sweep (2026-11-09)"; novelty NOT established.
- **Implications for which theorems unlock most models.** These come from verified sources plus my labelled derivations:
  - A3 (cusp) occurs in M-c, M-f, the King's case of M-b, and the lattice wave equation. **An A3 theorem unlocks the most already-classified models.**
  - Conical, non-smooth points occur in graphene's Dirac points, the massless wave equation, and (own derivation) Grover/Yee at the Courant limit.
  - M-a appears to need only A1/A2/D4 (own derivation), i.e. it may already be within OscInt's hypotheses.
- **Quick wins I noticed (own algebra, unverified as citations):**
  - M-d is M-b at t′/t = 1/4.
  - The King's graph is M-b at t′/t = 1.
  - M-e at the Courant limit, M-i and M-j share cos ω = a cos k1 + b cos k2.
  - So a census of two parameter families (t–t′, and the a, b cosine family) would cover M-a, M-b, M-d, M-e, M-i and M-j at once.
