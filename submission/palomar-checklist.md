# Palomar Registry & Multi-Platform Maintainer Checklist

Complete the manual decisions below before making any external submission from branch `palomar/submission-prep`.

## 1. Before Submitting to Palomar Registry (`submit.palomar-registry.org`)

- [ ] **Choose a permissive repository license (`Apache-2.0` or `MIT` recommended):**
  - Both `Apache-2.0` and `MIT` are accepted by **Palomar Registry** AND required by **Lean Pool** (do **not** use `CC-BY-ND-*`).
  - Add the full SPDX legal text as a single `LICENSE` file at the **repository root** (`D:\work\sharp-L1-interpolation\LICENSE`).
  - Update `project.license` in `Lean/formalization.yaml` from `"PENDING-MAINTAINER-CHOICE"` to the exact matching SPDX identifier (`"Apache-2.0"` or `"MIT"`).
- [ ] **Confirm human identity fields in `Lean/formalization.yaml`:**
  - Verify `project.authors` and `project.responsible_maintainers` list the maintainer name(s) you wish published (currently `["Lijails"]`; Palomar forbids listing AI models in those two fields).
- [ ] **Merge & verify full Linux Comparator CI:**
  - Review and merge PR #8 (`docs/english-paper` $\to$ `main`) first if keeping `main` clean, then review and merge the `palomar/submission-prep` PR so GitHub Actions (`.github/workflows/palomar.yml`) runs `scripts/check-lean-sources.py` + `lake build` + Linux `bubblewrap` `lake comparator` (checking NanoDa + Lean kernel) on the exact submission commit.
  - Record the resulting **full 40-character commit SHA** on `main` (Palomar rejects branch/tag names).
  - Optionally run Palomar's official preflight workflow (`PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml` with `mode: full`, `execution_profile: palomar-standard-v1`).
- [ ] **Submit to Palomar Registry:**
  - Open <https://submit.palomar-registry.org/> with:
    - Repository: `Ye-Chern/sharp-L1-interpolation`
    - Commit: `<40-char SHA>`
    - Selected project directory: `Lean`
    - Metadata path: `Lean/formalization.yaml` (default under `Lean`)
    - Comparator configuration path: `Lean/comparator.json`
  - Review the private mechanical report and AI editorial review, then consent to register and record the resulting public **Palomar URL**.

## 2. Before Submitting to Hexagon (`hexagonmath.org`)

- [ ] Review [`submission/hexagon/README.md`](hexagon/README.md), [`submission/hexagon/paper_hexagon.tex`](hexagon/paper_hexagon.tex), and [`submission/hexagon/metadata.json`](hexagon/metadata.json).
- [ ] Fill in submitter ORCID iD, choose a Hexagon distribution license (`CC BY 4.0`, `CC BY-SA 4.0`, or `CC0 1.0`), confirm `humanUnderstanding` (`"all"` or `"some"`), set `rightsConfirmed: true`, and insert the registered Palomar URL in `formalizations`.

## 3. After Palomar Registration: Lean Pool (`LeanPool/lean-pool`)

- [ ] Review [`notes/lean-pool-feasibility.md`](../notes/lean-pool-feasibility.md).
- [ ] If pursuing Lean Pool inclusion (which prioritizes Palomar-accepted projects), use a dedicated follow-up branch to split the 6 `>200`-line proofs in core `SharpL1`, clear `weak.linter.mathlibStandardSet = true`, drop the obsolete v0.2 `Certificate/` / `SharpL1Data/` / `Audit.lean` files from the Lean Pool export, and open an issue or PR on `LeanPool/lean-pool`.
