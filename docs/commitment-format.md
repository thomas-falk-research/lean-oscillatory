# Statement commitment format (version 1)

A commitment is the SHA-256 (`sha256sum`) of a text file produced independently by
`tools/lean/CommitEnv.lean` (from the imported environment) and `tools/src/canon.rs` (from the `leanexport`
stream). `make commit` fails unless the two files are byte-identical.

Closure. Start from the statement constant. A constant contributes references from: its type; the value of a
`def` or `opaque` (never the proof of a theorem); the `all` and constructor lists of an inductive; the parent
inductive of a constructor; the `all` list of a recursor; constants and projection structure names inside these
expressions. The closure is the least set closed under these references.

Order. Constants are processed in byte order of their name token. Each constant's expressions are emitted in
post-order (application: function, then argument; binders: domain, then body; `let`: type, value, body;
projection: the structure term; constant: its universe levels), then its `D` line.

Tokens. A name `N…;` concatenates `s<len>:<utf8>` for string parts and `n<k>.` for numeric parts (self-delimiting).
Levels: `L<i> z | s a | m a b | i a b | p <name>`. Expressions: `E<i> b k | S l | c <name> <n> l₁…lₙ | a f x | l t b |
f t b | t ty v b | n <decimal> | r <len>:<utf8> | j <name> <idx> s`. Identical lines receive one id (structural
sharing by line content, so both producers' internal sharing is irrelevant). `mdata` is transparent.
Declarations: `D axiom|thm|def|opaque|quot|induct|ctor|rec <name> <#lparams> <lparams> T <type> …` with the value
(`V`) of defs and opaques, `safe|unsafe|partial`, the quotient kind, and the inductive, constructor and recursor
counts and flags. The file starts with `OSCINT-COMMIT 1 <root name>`.

What it does not commit to. Binder names, binder annotations (explicit/implicit/instance) and the `let`
non-dependency flag: `leanexport` 3.1.0 shares subterms up to these, so the export does not determine them
(VALIDATED 2026-11-05: an earlier format that included them disagreed between producers on these fields alone).
They do not affect the kernel's meaning of a proposition. Elaboration-level facts such as notation, coercion
display or instance priorities are not committed either; the fidelity reviews read the source.
