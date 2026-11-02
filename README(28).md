# Families through ρ|G_E: the mixed refinement (2 November 2026)

Author: Dula.

Labels: [T] theorem or exact computation; [N] numerical; [C] supported by data, not proved; [S] a reading.

Nothing here proves H1, H2 or Artin's conjecture for ρ.

## 1. The case-(iii) nearly ordinary deformation problem is unobstructed [T]

Setting (note, Proposition `prop:no`): E imaginary quadratic, ℓ a prime split in E (ℓ𝒪_E = v v̄), ρ(Frob_ℓ) not scalar with eigenvalues α ≠ β and eigenlines L_α, L_β for Frob_v, and H¹(G_{ℚ,S}, ad⁰ρ ⊗ ℚ̄_ℓ) = 0 (Leopoldt for K₁₂ at ℓ; verified for ℓ = 2, 3, 5, 7, 11, 31, 41, 61, 71). Fix σ ∈ G_ℚ non-trivial on E with σD_vσ⁻¹ = D_v̄. Case (iii) is the choice of lines L_v = L_α at v and L_v̄ = ρ(σ)L_β at v̄. Residually at ℓ = 2 this is the mixed refinement (T_v, T_v̄) ≡ (x, y).

Let D be the functor of deformations of ρ|G_E to Artinian local ℚ̄_ℓ-algebras with residue field ℚ̄_ℓ, with determinant det ρ, unramified outside ℓ·1951 and ∞, and nearly ordinary at v and v̄ for lifts of L_v and L_v̄. These lifts are unique, because α ≠ β.

**Lemma.** D is pro-represented by ℚ̄_ℓ[[t]]. Its weight map sends t to an infinitesimal weight (w, w) with w ≠ 0.

*Proof.*
- The tangent space is the Selmer group H¹_L(G_{E,S}, ad⁰ρ). It has dimension 1, with infinitesimal weight (w, w) and w ≠ 0. This is Proposition `prop:no`(iii) of the note.
- The local conditions are smooth.
  - At v: the nearly ordinary condition is the image of H¹(D_v, b⁰), where b⁰ is the trace-zero Borel subalgebra for L_v. Its characters are 1 and α/β. Both H²(ℚ_ℓ, 1) = H⁰(ℚ_ℓ, ℚ̄_ℓ(1))^∨ and H²(ℚ_ℓ, α/β) = H⁰(ℚ_ℓ, (β/α)(1))^∨ vanish, since a finite-order character is never the cyclotomic one. So H²(D_v, b⁰) = 0. The same holds at v̄.
  - At the place above 1951: the local H² is H⁰(D_w, ad⁰(1))^∨ = 0. The H-direction is unramified with Frobenius eigenvalue N(w) ≠ 1 on the twist, and the other two directions are ramified (inertia acts by χ^{±1}).
- Greenberg–Wiles count:
  - h¹_L − h¹_{L^⊥}(ad⁰(1)) = h⁰(ad⁰) − h⁰(ad⁰(1)) + Σ_{v∈S}(dim L_v − h⁰(G_v, ad⁰)).
  - At v and v̄: dim L_v = 3 (local H¹(ad⁰) has dimension 2 + 1 + 1, and the condition kills the F-line) and h⁰ = 1 (only the H-direction is invariant, since α ≠ β). That gives 2 + 2.
  - At the place above 1951: dim L_w = h⁰ (the local H¹ is the unramified H-line). That gives 0.
  - At the complex place: 0 − 3.
  - Global: h⁰(ad⁰) = h⁰(ad⁰(1)) = 0.
  - The total is 1. So h¹_{L^⊥}(ad⁰(1)) = h¹_L − 1 = 0.
- The vanishing dual Selmer group kills Ш²(ad⁰). It also makes H¹(G_{E,S}, ad⁰) → ⊕_v H¹(G_v)/L_v surjective (Poitou–Tate). With smooth local conditions, every small extension of a deformation in D lifts to one in D. So D is formally smooth of dimension h¹_L = 1. ∎

**Consequences.**
- [T] The generic fibre of the case-(iii) nearly ordinary deformation space of ρ|G_E is a smooth curve germ at the Artin point. Its weight map has rank one there, in the parallel direction. So there is an ℓ-adic analytic one-parameter family of Galois representations of G_E through ρ|G_E, nearly ordinary at v and v̄ with the mixed lines.
- In case (ii), the base-change lines, the tangent has dimension 2 and the dual Selmer group dimension 1. That problem may be obstructed.
- [S] The family can carry classical points only at parallel weights κ_v = κ_v̄. Such points are cohomological Bianchi forms that are not base changes: at ℓ = 2 they have U_v ≢ U_v̄ mod 2.
  - If the weight curve is the diagonal, there are such points at every parallel weight near κ₁, for instance k = 1 + 2^m for m large. These are nearly ordinary with distinct Hodge–Tate weights, so de Rham, and Fontaine–Mazur predicts that they are automorphic.
  - If the weight curve leaves the diagonal at some finite order, classical points near ρ|G_E are at most isolated.
  - The lemma decides the first order only. That the second-order defect (κ_v − κ_v̄)'' does not depend on the parametrisation makes it a well-defined test. Computing it needs explicit second-order class field theory, which we do not have.
- [S] Calegari–Mazur, Cor. 1.4 (conditional on Strong Leopoldt), say that for a finite non-dihedral image over an imaginary quadratic field, a diagonal infinitesimally classical weight forces an odd descent. Proposition `prop:no`(iii) gives a diagonal weight for the even ρ. So either their corollary presupposes Galois-compatible lines, as in case (ii), or one of the two statements needs a hypothesis that we have not identified. The note reads case (iii) as the exceptional "even" case of their §1. We could not read their §8.2 to settle this.
- What H1 would need along this route:
  - (a) the family's weight curve is the diagonal;
  - (b) its classical members are automorphic, which needs automorphy lifting at ℓ = 2 for GL₂ over E in ordinary weight;
  - (c) classicality of the weight-one specialisation.
  Over ℚ, (c) is Buzzard–Taylor's step for odd ρ. Over E no such step is known: forms of Artin type contribute to no cohomology.

## 2. Where would classical points sit, and how to test for them

- **The test point.** At ℓ = 2 the weight space near the Artin weight κ₁ (trivial character of ℤ₂^×) contains:
  - weight 2 with the wild nebentypus χ₋₄ at v and at v̄ (weight character z·χ₋₄(z), at distance 1/4 from κ₁, in the same component since κ(−1) = 1, and parallel because the nebentypus at 2 is χ₋₄∘N);
  - weight 3 with trivial nebentypus at 2 (distance 1/8).
- Weight 2 with χ₋₄ at v and v̄ uses scalar coefficients, so the existing engines apply at level N·4·𝒪_E. A classical point of the family at that weight is a characteristic-0 eigenform of level N·4·𝒪_E, nebentypus (det ρ_A)^{±1}∘N · χ₋₄∘N, with mod-2 residual ρ̄_A|G_E and the mixed refinement (U_v, U_v̄) ≡ (x, y) or (y, x).
- At level N·4·𝒪_E with nebentypus of conductor exactly v²v̄² at 2, every form is new at v and v̄. U_v and U_v̄ are then determined by the local components, and a base change has U_v = U_v̄.
- For ρ itself the level 1951·4·𝒪_E has index 1951²·36 ≈ 1.4·10⁸, and weight 3 at 1951·𝒪_E has about 1.5·10⁷ unknowns. Both are out of reach here, so the test is run on models.

**Tools (new).**
- `eis_shape.py`, `analyze_t163.py`: the Eisenstein systems and the asymmetric part of saved Hecke matrices (§§4–5); `check23q.py`: the control of §5.
- `bianchi4.py`: the component 𝒪/4𝒪 = ℤ/4 × ℤ/4 (points of P¹, scalars, the project's v ↔ t ≡ 0 mod 2 convention), a quadratic character spread over several components, and U at v and v̄ (right cosets (1 b; 0 π), weight 1). `bianchi4big.py` is the block-Lanczos version.
- `exact_hecke.py`: the cocycle space in its canonical basis for every prime, Hecke matrices, and CRT with rational reconstruction.
- `m1_lattice.py`:
  - a leave-one-out check of the reconstruction;
  - exact commutativity over ℚ;
  - a Hecke-stable ℤ-lattice (closure of ℤ^D under all operators, by HNF) with integral matrices;
  - reduction mod 2 and the generalized eigenspaces over F₄.
  By Brauer–Nesbitt the dimension of a generalized eigenspace mod 2 is the number of characteristic-0 eigen-systems (with multiplicity) that reduce to it.

## 3. The odd dihedral model at 23 (control, `run_level4.py d23`, `m1_exact.py`, `m1_lattice.py`) [T]

ρ₂₃ is the weight-one form η(z)η(23z) (odd, CM by ℚ(√−23)). Over E = ℚ(√−7), 23 splits, and 2 = v v̄. ρ̄₂₃(Frob₂) has eigenvalues ω, ω² (a₂ = −1), so x ≠ y.

- **Level and nebentypus.** Level 23·4·𝒪_E (index 20 736), nebentypus ((−23/·)χ₋₄)∘N.
- **Dimension.** dim H¹ in characteristic 0 is 76 at two primes P. All 21 operators commute.
- **Base change.** The base-change-symmetric subspace (common kernel of T_q − T_q̄ for q = 11, …, 79 and of U_v − U_v̄) has dimension 10. This equals dim S₂^new(Γ₀(92), (92/·)) = 10 (PARI). The χ₋₇-twist (−644/·) is odd, so it contributes no weight-2 forms. This checks the engine with the new 𝒪/4𝒪 component and the U operators.
- **The other 66 dimensions** are not base changes.
  - 8 of them are Eisenstein classes (§5): at all 18 good operators their eigenvalues are u₁π + u₂π̄ with u₁, u₂ = ±1, for example a(3) = ±6, a(5) = ±10 and a(𝔮₁₁) = ±4 (`eis_shape.py`, `lvl4_d23_P1048273_eis.json`). As §5 predicts, none of them is symmetric.
  - The other 58 are cuspidal. They are mostly CM-type (T_𝔮 = 0 on large subspaces at primes inert in quadratic extensions of E).
- **Exact Hecke matrices over ℚ.** `m1_exact.py` computes and caches the data at each prime (`cache_m1_P*`). Its own analysis step over large rationals was stopped at the 30-minute limit for background jobs (a hold); `m1_lattice.py` replaced it and works from the cache.
  - 15 operators from 20 primes; the leave-one-out check at the 20th prime gives 0 mismatches.
  - Denominators are up to 98 bits in the canonical basis. All matrices commute exactly.
  - A Hecke-stable lattice is reached after 4 HNF iterations, with integral matrices.
- **Mod 2.** The characteristic-0 systems that agree with ρ̄₂₃|G_E at all 13 good operators have total dimension 24, split by (U_v, U_v̄) mod 2:
  - (ω, ω): 1 and (ω², ω²): 1 — ordinary, pure refinement;
  - (ω, 0), (ω², 0), (0, ω), (0, ω²): 1 each — ordinary at one place only;
  - (0, 0): 18 — non-ordinary at both places;
  - **mixed (ω, ω²) or (ω², ω): 0.**
- **Reading [S].** In the odd (non-exceptional) dihedral case, no classical form at the first wild weight-2 point carries the mixed refinement. This is what Calegari–Mazur predict. The CM families through ρ₂₃|G_E come from E(√−23), whose cohomological CM types are lifted from ℚ(√−23). At v and v̄ they pick the unit root over the same prime of ℚ(√−23), so the refinement is pure.

## 4. The even tetrahedral model of conductor 163 (`a4scan.py`, `t163_field.py`, `t163_traces.py`, `run_t163.py`, `analyze_t163.py`, `eis_shape.py`)

**Why this model.** It is the closest analogue of ρ that is small enough to compute: an even, non-dihedral (so not CM) Artin representation, unramified at 2, with 2 split in E = ℚ(√−7) and distinct residual Frobenius eigenvalues at v. It is the Calegari–Mazur "even" exceptional case without CM. The even icosahedral case starts at conductor 1951 (ρ itself), and even octahedral conductors start near 2000, so both are too large.

**The representation [T].**
- The totally real A₄ quartics with |disc| ≤ 3·10⁶ number 62 (`a4scan.py`, PARI `nflist`). The smallest is x⁴ − x³ − 7x² + 2x + 9, with disc 163² and Frob₂ of order 3 (2 = 𝔭₁𝔭₃).
- Its splitting field M₁₂ = ℚ[y]/(y¹² − 23y¹⁰ + 125y⁸ − 231y⁶ + 125y⁴ − 23y² + 1) is totally real, with disc 163⁸ and class number 1 (GRH).
- The ray class group of M₁₂ mod 163·∞ is (54, 2, 2, 2, 2). Of its 31 index-2 subgroups, 3 are Galois-stable. Exactly one gives an extension unramified at every finite prime (`t163_cands_163_inf.json`): K₂₄ = M₁₂(√α).
- K₂₄/ℚ has group SL(2,3), not A₄ × C₂: all 117 primes below 3000 with Frobenius in V₄ are inert in K₂₄/M₁₂ (`t163_traces.log`).
- ρ₀: G_ℚ → SL(2,3) ⊂ SL₂(ℂ). tr ρ₀(Frob_p) is read off the order of Frob_p (1: 2, 2: −2, 3: −1, 4: 0, 6: 1). Then ρ_t = ρ₀ ⊗ ψ, with ψ the cubic character of conductor 163 (Conrey 58).
  - ρ_t has conductor 163: inertia at 163 has order 3, and ψ cancels one of its eigenvalues.
  - det ρ_t = ψ², and ρ_t is even.
  - Traces for p < 3000 are in `t163_traces.json`.
- **Residual mod 2:** ρ̄_t^{ss} = ψ̄·(θ ⊕ θ⁻¹), with θ: A₄ → C₃. This is residually reducible (Eisenstein); a check against tr ρ₀ mod 2 holds at all 429 primes. Its Frobenius eigenvalues at 2 are distinct, because 2 is not a cube mod 163.

**The first wild weight-2 point.**
- Level 163·4·𝒪_E (163 splits in E), index 968 256; nebentypus (det ρ_t)⁻¹∘N·χ₋₄∘N = (ψχ₋₄)∘N.
- Base change from ℚ: only ψ²χ₋₄χ₋₇ (even) contributes; the character ψ²χ₋₄ is odd and has no weight-2 forms. dim S₂^new(Γ₀(4564), ψ²χ₋₄χ₋₇) = 652. Among these newforms, 4 have CM by E (conductors v²𝔭, v²𝔭̄, v̄²𝔭, v̄²𝔭̄, §5); their base changes are Eisenstein. The other 648 form 324 pairs {f, f ⊗ χ₋₇}. So there are 324 cuspidal base changes. (A first count of 326 = 652/2 ignored the CM forms; §5.)
- Eisenstein classes (§5): 8, of which 4 are symmetric (the base changes of the 4 CM forms) and 4 are not.
- Prediction if there is no cusp form that is not a base change: dim H¹ = 324 + 8 = 332, symmetric part 328, asymmetric part 4, all Eisenstein.

**Result [T|A].** `run_t163.py 0 1` (P = 1048273, ζ₃ ↦ 67597; 32 minutes; log `run_t163_p0e1.log`, 66 lines, all read):
- Closure: 519 201 classes, 1 090 266 equations. Markowitz core 75 016 × 31 865, nnz 13 665 581, no free classes.
- Kernel: six block-Lanczos solves (b = 64) give kernel rank 333, equal to the Krylov bound 333, so the kernel is complete. All 7 746 048 relator equations hold on every vector. dim H¹ over F_P = 332 (the coboundary δm_par removed).
- 15 operators (r7, (3), (5), T_𝔮 and T_𝔮̄ for 𝔮 above 11, 29, 37, 43, 53, U_v, U_v̄) commute. The base-change-symmetric subspace has dimension 328; the asymmetric rank is 4.
- `analyze_t163.py`: the asymmetric part consists of 4 generalized eigenspaces, each of dimension 1. At all 13 good operators their eigenvalues have the shape u₁π + u₂π̄ (u₁, u₂ ∈ μ₆), not s + N(𝔮)t.
- `eis_shape.py` (μ₆): exactly 8 one-dimensional systems have the shape u₁π + u₂π̄ at all good operators; 4 are symmetric and 4 are not. For example a(5) = 10 for all 8, and (a(𝔮₁₁), a(𝔮̄₁₁)) = (−463 978, −193 582) for an asymmetric one. U_v ≠ U_v̄ on the asymmetric ones.
- Characteristic 0: dim ≤ 332 (it is at most the dimension over F_P), and dim ≥ 324 + 8 (cuspidal base changes and Eisenstein classes, §5). So **H¹(Γ₀(163·4·𝒪_E), ℂ((ψχ₋₄)∘N)) has dimension 332: the 324 cuspidal base changes and 8 Eisenstein classes. There is no cusp form that is not a base change.**

**Reading [S].**
- A base change has U_v = U_v̄, so no cusp form at this point has the mixed refinement. The asymmetric classes are Eisenstein, attached to reducible representations θ₁ ⊕ θ₂; they are not points of a family of irreducible representations through ρ_t|G_E.
- So a case-(iii) family through ρ_t|G_E has no classical point at the first wild weight-2 point, at minimal level. The same holds for the odd dihedral control (§3), where Calegari–Mazur predict it.
- Since ρ̄_t is reducible modulo 2, the comparison is made in characteristic 0 only; there is no mod-2 analysis here.
- This is one test point at one level. It does not rule out classical points at other weights or at higher level. The nearer test points are weight 3 (distance 1/8) and weight 5 (distance 1/16) with trivial nebentypus at 2. They need coefficient modules of dimension 4 and 16, which the engines do not have yet. For t163, weight 3 at level 163·𝒪_E (index 26 896) would be a small computation once that is written.

## 5. Eisenstein classes in H¹ and the base-change counts [T|A]

The base-change counts above and in `bianchi2/bc_counts.py` count newforms over ℚ in pairs {f, f ⊗ χ₋₇}. A newform with CM by E is its own twist, and its base change to E is not cuspidal. This section says where those forms go, and where the Eisenstein classes of H¹ are.

- **The boundary** (standard; checked below). Let Γ = Γ₀(𝔫) ⊂ PGL₂(𝒪_E) with nebentypus ε trivial on −1 (here ε = ε′∘N), of full conductor 𝔫.
  - At the cusp attached to a coprime factorisation 𝔫 = 𝔡𝔡′, the torus diag(u, u′), u, u′ = ±1, acts on H¹ of the unipotent lattice by u/u′ and on the coefficients by ε_𝔡(u′)ε_𝔡′(u).
  - So the cusp contributes 2 dimensions to H¹(∂) when ε_𝔡(−1) = ε_𝔡′(−1) = −1 (a regular cusp), and 0 otherwise. The other cusps carry no invariants, because ε has full conductor.
  - By Poincaré–Lefschetz duality, the image of H¹(Γ) in H¹(∂) has half the dimension of H¹(∂).
  - By Kostant, the degree-one boundary classes come from the Weyl elements of length one. Their Hecke eigenvalues are θ₁(𝔮) + θ₂(𝔮), with θ₁, θ₂ Hecke characters of E of infinity types z and z̄: a(𝔮) = u₁π + u₂π̄ for 𝔮 = (π), u₁, u₂ roots of unity. Pairs of finite order (eigenvalues s + N(𝔮)t) occur in degrees 0 and 2, not in degree 1.
- **Symmetric Eisenstein classes are base changes of CM forms.** E(θ₁, θ₂) is symmetric (T_𝔮 = T_𝔮̄) when θ₂ = θ₁^σ. It is then the base change θ₁ ⊞ θ₁^σ of the CM form AI(θ₁) over ℚ, which lies in the base-change space. So the symmetric part of H¹ is (dim S − c)/2 + e_sym, with c the number of newforms with CM by E in S and e_sym the number of symmetric Eisenstein classes, plus any symmetric cusp forms that are not base changes (none in the cases below).
- **Checks.**
  - Level 23·𝒪_E, nebentypus (·/23)∘N (`check23q.py`). Both local components are odd, so the two cusps 𝔡 = 𝔭, 𝔭̄ are regular. dim H¹ = 8. PARI: S₂(Γ₀(161), (161/·)) has dimension 14, namely 2 newforms with CM by ℚ(√−7) (one Galois orbit) and 12 others. Predicted: (14 − 2)/2 + 2 = 8. `eis_shape.py` finds the 2 Eisenstein systems, both symmetric (a(3) = 6, a(5) = −10).
  - d23 (level 92·𝒪_E, §3). All four local components of the nebentypus are odd, so the regular cusps are the 8 factorisations with |𝔡| odd. Symmetry would need 𝔡′ = σ𝔡, which forces |𝔡| = 2. So all 8 Eisenstein classes are asymmetric. Found: exactly 8 one-dimensional systems of the shape u₁π + u₂π̄ (u = ±1), none symmetric.
  - t163 (§4): 8 regular cusps (exactly one of v², v̄² in 𝔡; 𝔭, 𝔭̄ free), 4 of them symmetric. Found: 8 systems, 4 symmetric.
  - Level 1951·𝒪_E (the Question 3 records). 1951 is inert in E (the index is 1951² + 1), so the level has two cusps, neither regular, and no newform has CM by E (1951 is not a norm from E). The counts 161 and 649 are unaffected.

