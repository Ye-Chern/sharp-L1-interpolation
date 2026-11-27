# Hexagon Offline Submission Package

> **Important:** This directory is prepared for **offline review only**. No automated or external submission to `hexagonmath.org` has been performed.

Per [Hexagon's policy and OpenAPI v1.13.0-beta specification](https://hexagonmath.org/about), Hexagon accepts LaTeX paper sources (`paper_hexagon.tex`), separates **human contributors** (authenticated via ORCID iD; AI systems cannot be listed as `authors`) from **`aiSystems`** / **`provenance`**, does **not** host Lean code directly, and links to verified formalizations on **Palomar Registry** via `formalizations`.

## Contents

- [`paper_hexagon.tex`](paper_hexagon.tex) — Standalone English manuscript adapted from [`../../paper.tex`](../../paper.tex) with human author entry (`Lijails`) and an explicit **Acknowledgments and AI Contributions** section naming GPT 6.2 Astra, GPT 6.2 Sol, Gemini 4 Neon, and Gemini 4 Hydrogen.
- [`metadata.json`](metadata.json) — Complete Hexagon `SubmissionMetadata` payload ready for final maintainer choices.

## Maintainer Pre-Submission Checklist

Before creating a deposit on <https://hexagonmath.org>:

1. **Identity & ORCID (`authors[0]`):** Sign in to Hexagon with ORCID, replace `"Lijails"` / `orcid` placeholder in `metadata.json` (and update `\author{...}` in `paper_hexagon.tex` if publishing under a full legal/academic name).
2. **Human Understanding Declaration (`humanUnderstanding`):** Choose `"all"` or keep `"some"` with the included detailed `provenance` account.
3. **Distribution License (`license`):** Replace the placeholder in `metadata.json` with exactly one Hexagon-accepted SPDX string:
   - `"CC BY 4.0"`
   - `"CC BY-SA 4.0"`
   - `"CC0 1.0"`
4. **Palomar Formalization Link (`formalizations`):** Once registered on Palomar Registry, replace `https://palomar-registry.org/PENDING-PALOMAR-ID` with the canonical immutable Palomar record URL.
5. **Confirm Rights (`rightsConfirmed`):** Set `"rightsConfirmed": true` and review `correctnessConfirmed`, `communityInterestConfirmed`, and `citationsConfirmed`.
6. **Upload & Compile Preview:** Upload `paper_hexagon.tex` (plus optionally ancillary provenance notes if desired under Hexagon's `anc/` rules), verify the server preview PDF builds cleanly, and commit.
