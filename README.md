# Breaking Resonance: Lean 4 formalization

Companion repository for N. Bou-Rabee, *Breaking Resonance: Square-root acceleration for Metropolis-adjusted randomized Hamiltonian Monte Carlo* (2026).

## The result

The paper proves that Metropolis-adjusted Hamiltonian Monte Carlo with velocity Verlet and a random integration time drawn from a non-resonant law reaches total variation accuracy epsilon from a warm start after O~(sqrt(kappa d) + sqrt(L_H) (d/m)^{3/4}) gradient evaluations, for targets exp(-U) with m I <= Hessian(U) <= L I and an L_H-Lipschitz Hessian, kappa = L/m. The bound holds for every non-resonant integration-time law, including the uniform, exponential and decreasing triangular laws. The Hessian condition cannot be dropped for fixed step sizes: without it there are targets in the class on which the cost is at least of order kappa^{2/3}, up to logarithmic factors, even from a warm start (Theorem 2). A Gaussian lower bound (Proposition B.1) shows that the number of gradient evaluations is at least of order sqrt(kappa).

## Key ideas

**Non-resonant integration times (Definition 2.1).** With a fixed integration time, a mode of a Gaussian target whose half-period divides that time returns to plus or minus its initial position, and the chain does not mix in that coordinate. A duration law tau is non-resonant when E cos(omega tau) <= 1 - delta for all frequencies omega >= 2 sqrt(m), with mean of order 1/sqrt(m). The condition is checked for the uniform, exponential and decreasing triangular laws (Lemma 5.4), including the effect of rounding the duration to a whole number of Verlet steps (Lemma 5.3).

**Entropy contraction of the proposal (Proposition 6.8).** For the triangular law with integration time 4/sqrt(m), the law of the proposed position is closer to the target in relative entropy than the initial law, by a fixed factor, up to the Verlet energy error. The argument adapts the weighted entropy estimate of Mitra, Srinivasan, Wang and Wibisono (arXiv:2607.12902) from the exact Hamiltonian flow to velocity Verlet, using the exact expression for the energy error of a Verlet step (Lemma 6.1) and the free-transport entropy inequality of Persistence Pays (arXiv:2610.35781).

**From entropy contraction to conductance (Lemma 6.9).** A general lemma for Metropolis-adjusted kernels: if the proposal contracts relative entropy from conditioned starts and is accepted with high probability on a set of large mass, the kernel has restricted conductance bounded below. This gives Proposition C for the triangular law.

**Fourier comparison (Lemmas 5.1 to 5.3, Propositions A and B).** The sampler is reversible, and the Dirichlet forms of the adjusted kernels for two duration laws are compared through the real parts of their characteristic functions. This transfers the conductance bound from the triangular law to every non-resonant law and gives a lower spectral bound. Restricted conductance and the lower spectral bound give mixing from a warm start.

## This repository

**License.** Apache License 2.0 (see LICENSE), the license of Mathlib.

---

Theorem 1, Theorem 2 and Proposition B.1 are Lean-verified for the actual Metropolis position kernel, with the manuscript's assumptions and constants. As in the paper, the proof of Theorem 1 takes two results from the literature as explicit inputs: Talagrand's transport-entropy inequality (Lemma 6.3) and the interpolation estimate of Persistence Pays (Lemma 6.4).

**Start with [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md).** It lists the certificates, the build and the axiom audit.

## Main certificates

- [TheoremOne.lean](BreakingResonance/TheoremOne.lean): `theoremOne` proves total variation accuracy of the actual position kernel from an L2-warm start, with the explicit step-size and iteration constants. [UpperAssembly.lean](BreakingResonance/UpperAssembly.lean): `theoremOne_explicit_normalized` checks the law-specific constants.
- [TheoremTwo.lean](BreakingResonance/TheoremTwo.lean): `theoremTwo` proves the gradient lower bound for the explicit target of Section 7, the actual rounded Metropolis kernel, and every duration law satisfying the stated conditions.
- [GaussianLowerBound.lean](BreakingResonance/GaussianLowerBound.lean): `gaussianGradientLowerBound` proves Proposition B.1, including the crossing argument on the actual position path.
- [RestrictedMixing.lean](BreakingResonance/RestrictedMixing.lean), [LowerSpectralBound.lean](BreakingResonance/LowerSpectralBound.lean), [RestrictedVerlet.lean](BreakingResonance/RestrictedVerlet.lean): `propositionA`, `propositionB`, `propositionC`.
- [ProposalEntropy.lean](BreakingResonance/ProposalEntropy.lean): `verlet_triangular_proposal_entropy` proves Proposition 6.8. [GeneralEntropyConductance.lean](BreakingResonance/GeneralEntropyConductance.lean): `general_entropy_conductance` proves Lemma 6.9.

## Verification

The aggregate build and the axiom audit passed for **797 named declarations**. This includes supporting definitions and lemmas, not just the main results. No `sorry`, `admit`, `sorryAx` or new axioms are used. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` occur.

The project pins Lean 4.34.0-rc2 and mathlib revision `85e3a25e006c35636f0e53b0e9296caca2685bc0` in the [Lake configuration](lakefile.toml) and [toolchain file](lean-toolchain). With those dependencies installed, `lake build` builds the library and `lake env lean AxiomAudit.lean` runs the audit. See [lake_build.log](lake_build.log) and [axiom_audit.log](axiom_audit.log) for the successful final run, and [SHA256SUMS](SHA256SUMS) for the hashes of the checked sources.

## Statement fidelity and records

- [THEOREM_MAP.md](THEOREM_MAP.md): Lean declarations for each manuscript statement.
- [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md): certificates, build and audit record.
- [NOTICE.md](NOTICE.md): attribution and source manifests for the reused sources in `PersistencePays/` and `SLT/`.

Source: manuscript of 2026-11-23; the reports use its numbering.
