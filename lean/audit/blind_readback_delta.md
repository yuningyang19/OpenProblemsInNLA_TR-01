# Independent blind delta readback: joint upper-draw interface

BLIND_DELTA_READBACK_COMPLETE. Manuscript correspondence NOT_ASSESSED. This bounded follow-up inspects the actual revised GeneralSamplingJointExpected and GeneralSamplingJoint modules and the declaration general_sampling_joint_saturated_sharp from SamplingInterfaceBridges. No manuscript, reference Expected.lean, comparison verdict, or generator report was consulted. The earlier blind report and JSON are retained unchanged as historical observations of their bound bytes. No build, axiom audit, or compiled/source identity check is claimed here.

## Revised joint declaration

Let n=|α|, θ±=(1±ε/4)k/n, 0<ε<1, 1≤k≤n. The general_sampling_joint theorem still takes an arbitrary probability space, an entrywise measurable real n×r random frame X that is orthonormal almost everywhere, uniform k-subset selector S, and lower and upper Boolean-vector maps Eminus,Eplus. S and Eminus are measurable and each is independent of X. S has the exact uniform-subset law; Eminus has the full product Bernoulli(θ-) law. No mutual independence of the sampling maps is required.

ALL FOUR requirements on Eplus are now implications with antecedent θ+<1:

1. Measurable Eplus.
2. Independence of Eplus from X.
3. The full product Bernoulli(θ+) law for Eplus.
4. Its Gram failure probability at threshold ε/4 is at most γ.

The lower failure probability at ε/4 remains bounded by γ unconditionally. The conclusion remains

    P(||(n/k)XᵀP_S X-I||₂>ε) ≤ 2γ+2 exp(-ε²k/48).

Thus for θ+≥1, including exact equality, no measurability, independence, marginal, or failure property of the supplied Eplus is required. Eplus is still syntactically a universally quantified map in the general theorem; it is not an existential probabilistic construction requirement and can be filled by any map in this branch. This resolves the earlier readback's specific observation about unconditional upper-draw measurability and independence in the old joint alias. The implementation supplies these two hypotheses to the old Bernoulli law bridge only after assuming θ+<1.

## Parameter-free saturated interfaces

The public general_sampling_joint_saturated in GeneralSamplingJoint has no Eplus variable at all, and concludes the same 2γ+2exp(-ε²k/48) bound. It requires θ+≥1, the lower draw's marginal/tail/measurability/independence, the fixed sample's uniform marginal/measurability/independence, and the same arbitrary-law frame assumptions.

The public general_sampling_joint_saturated_sharp in SamplingInterfaceBridges also has NO Eplus parameter, NO Eplus condition, and NO upper-draw existence or law premise. Precisely, for any probability space (Ω,μ), finite α with n=|α|, r,k∈N, and maps X:Ω→R^{n×r}, S:Ω→{k-subsets of α}, Eminus:Ω→{0,1}^n, assume:

- X is entrywise measurable and XᵀX=I_r almost everywhere.
- S and Eminus are measurable, and X is independent of each separately.
- 0<ε<1, 1≤k≤n, and θ+=(1+ε/4)k/n≥1.
- For every k-subset J, μ(S=J)=1/binomial(n,k).
- For every Boolean vector e, μ(Eminus=e)=product_i θ-^{e_i}(1-θ-)^{1-e_i}, with θ-=(1-ε/4)k/n.
- μ(||θ-⁻¹Xᵀdiag(Eminus)X-I_r||₂>ε/4)≤γ.

Then

    μ(||(n/k)XᵀP_S X-I_r||₂>ε) ≤ γ+exp(-ε²k/32).

The endpoint θ+=1 belongs to this theorem. k=n is allowed. The lower parameter lies strictly between zero and one under these hypotheses, and k,n are positive; no invalid probability parameter or zero sampling denominator is introduced. γ is any real satisfying the lower failure bound, which implies γ≥0. r need not be positive. The measurable-singleton structures on the finite sampling output types remain explicit. There is no finite/atomic restriction on Ω or μ, and no pointwise-in-ω failure assumption replaces the averaged joint probability.

These are statement-semantic conclusions only. No manuscript fidelity, mathematical proof closure, axiom closure, release authority, or “optimality” interpretation of the name sharp is inferred. The sharp theorem's source proof invokes finite-noise law transport and general_sampling_saturated_sharp, but those transitive proof bodies were outside this bounded delta inspection.
