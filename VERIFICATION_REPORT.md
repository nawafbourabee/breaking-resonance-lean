# Lean verification of the main results of Breaking Resonance

**Completed on 23 November 2026 for the manuscript of 2026-11-23.** Theorem 1,
Theorem 2 and Proposition B.1 have checked Lean proofs under the manuscript's
assumptions. The actual probability laws, the Metropolis position kernel and
the gradient count are defined in the project. As in the paper, Theorem 1
takes Talagrand's transport-entropy inequality (Lemma 6.3) and the
interpolation estimate of Persistence Pays (Lemma 6.4) as explicit inputs.

## Certificates

| Manuscript result | Lean declaration | Source |
|---|---|---|
| Theorem 1: mixing from a warm start | `BreakingResonance.theoremOne` | [TheoremOne.lean](BreakingResonance/TheoremOne.lean) |
| Theorem 1: law-specific constants of (3.4) | `BreakingResonance.theoremOne_explicit_normalized` | [UpperAssembly.lean](BreakingResonance/UpperAssembly.lean) |
| Theorem 2: necessity of Hessian regularity for fixed step sizes | `BreakingResonance.theoremTwo` | [TheoremTwo.lean](BreakingResonance/TheoremTwo.lean) |
| Proposition B.1: gradient lower bound for Gaussian targets | `BreakingResonance.gaussianGradientLowerBound` | [GaussianLowerBound.lean](BreakingResonance/GaussianLowerBound.lean) |
| Proposition A: mixing from restricted conductance | `BreakingResonance.propositionA` | [RestrictedMixing.lean](BreakingResonance/RestrictedMixing.lean) |
| Proposition B: lower spectral bound | `BreakingResonance.propositionB` | [LowerSpectralBound.lean](BreakingResonance/LowerSpectralBound.lean) |
| Proposition C: restricted conductance of the sampler | `BreakingResonance.propositionC` | [RestrictedVerlet.lean](BreakingResonance/RestrictedVerlet.lean) |
| Proposition 6.8: relative entropy of the proposal law | `BreakingResonance.verlet_triangular_proposal_entropy` | [ProposalEntropy.lean](BreakingResonance/ProposalEntropy.lean) |
| Lemma 6.9: entropy contraction implies restricted conductance | `BreakingResonance.general_entropy_conductance` | [GeneralEntropyConductance.lean](BreakingResonance/GeneralEntropyConductance.lean) |
| Lemma 5.1: reversibility | `BreakingResonance.verlet_gradient_reversibility` | [Reversibility.lean](BreakingResonance/Reversibility.lean) |
| Lemma 5.3: Fourier bounds after rounding | `BreakingResonance.roundedFourierBounds` | [RoundedFourierBounds.lean](BreakingResonance/RoundedFourierBounds.lean) |
| Lemma 5.4: the three duration laws | `BreakingResonance.triangular_example_fourier`, `uniform_example_fourier`, `exponential_example_fourier` | [BoundedDurationBounds.lean](BreakingResonance/BoundedDurationBounds.lean), [ExponentialExample.lean](BreakingResonance/ExponentialExample.lean) |

The declarations for every manuscript statement are listed in
[THEOREM_MAP.md](THEOREM_MAP.md).

## Build and audit

The 23 November 2026 aggregate Lake build succeeded (9,196 jobs). The build
ran in a temporary copy of the project with local package paths for the
pinned dependencies. The compiled project sources match the files in this
directory. The build used the pinned compiled mathlib distribution.

The closure contains 432 local modules including the audit. A separate run
of the axiom audit checked 797 named declarations. Every reported dependency
is in the set propext, Classical.choice, and Quot.sound. The project source
scan found no proof placeholders or custom axioms in the BreakingResonance
modules. Vendored source hashes match their manifests.

The logs are in [lake_build.log](lake_build.log) and
[axiom_audit.log](axiom_audit.log).

## Scope of the main certificates

Theorem 1 is checked for the manuscript assumptions (A1) to (A3), the
normalized position Gibbs law and the actual position kernel, with the
explicit constants of Section 3. Theorem 2 is checked for its explicit
target and gradient constants, from the product target construction through
the conditional acceptance bound and the gradient count. Proposition B.1
checks the expected-gradient lower bound for the diagonal Gaussian target,
with the stated coefficient and the pathwise crossing argument.
