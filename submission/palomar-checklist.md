# Palomar Registry & Multi-Platform Maintainer Checklist

Maintainer status & final submission checklist from `main` (following the `palomar/preflight-polish` PR).

## 1. Before Submitting to Palomar Registry (`submit.palomar-registry.org`)

- [x] **Choose a permissive repository license (`Apache-2.0`):**
  - Root [`LICENSE`](../LICENSE) (`Apache-2.0`) added and `project.license: "Apache-2.0"` set in [`Lean/formalization.yaml`](../Lean/formalization.yaml) (compatible with both Palomar Registry and Lean Pool).
- [x] **Confirm human identity fields in [`Lean/formalization.yaml`](../Lean/formalization.yaml):**
  - `project.authors` and `project.responsible_maintainers` list `["Lijails"]` (human-only per Palomar policy), while AI collaborators (`GPT 6.2 Astra`, `GPT 6.2 Sol`, `Gemini 4 Neon`, `Gemini 4 Hydrogen`, and helper models) are credited in `automation.methods`, `sources[0].contributors`, and `acknowledgements`.
- [ ] **Merge & verify full Linux Comparator CI:**
  - Review and merge the `palomar/preflight-polish` PR into `main` and confirm all GitHub Actions workflows (including `.github/workflows/palomar.yml`: `scripts/check-lean-sources.py`, `Lean/formalization.yaml` v0.4 schema validation, `lake build`, `Audit.lean`, and Linux `bubblewrap` `lake comparator` with NanoDa + advisory con-ron) pass on the exact target commit.
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

- [x] Filled in submitter ORCID iD (`0009-0004-1849-2354`), distribution license (`"CC BY 4.0"`), `humanUnderstanding: "some"`, and `rightsConfirmed: true` in [`submission/hexagon/metadata.json`](hexagon/metadata.json).
- [ ] Review [`submission/hexagon/README.md`](hexagon/README.md), [`submission/hexagon/paper_hexagon.tex`](hexagon/paper_hexagon.tex), and [`submission/hexagon/metadata.json`](hexagon/metadata.json), and replace the placeholder URL `https://palomar-registry.org/PENDING-PALOMAR-ID` in `formalizations` once Palomar registration completes.

## 3. After Palomar Registration: Lean Pool (`LeanPool/lean-pool`)

- [ ] Review [`notes/lean-pool-feasibility.md`](../notes/lean-pool-feasibility.md).
- [ ] If pursuing Lean Pool inclusion (which prioritizes Palomar-accepted projects), use a dedicated follow-up branch to split the 6 `>200`-line proofs in core `SharpL1`, clear `weak.linter.mathlibStandardSet = true`, drop the obsolete v0.2 `Certificate/` / `SharpL1Data/` / `Audit.lean` files from the Lean Pool export, and open an issue or PR on `LeanPool/lean-pool`.
