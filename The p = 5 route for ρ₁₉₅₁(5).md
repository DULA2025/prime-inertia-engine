# The p = 5 route for ρ₁₉₅₁

Nov 19, 2026 · Dula

## Summary

Over F′ = ℚ(i, √5), the mod-5 reduction of the even icosahedral ρ of conductor 1951 is modular, after a twist by a finite-order character (Theorem A). The proof gives an explicit elliptic curve A over F′ with an exact certificate that A\[5\] ≅ ρ̄₅ ⊗ φ. Caraiani–Newton 6.1 then makes A modular. So neither Lemma 2.2 (a general proof that the twisted X(5) is P¹) nor the Shepherd-Barron–Taylor paper is needed. The same A is ordinary up to a character at both primes over 5, which supplies input B0 of Step B.

What remains between Theorem A and Artin's conjecture for ρ:

- Step B, 5-adic automorphy of ρ restricted to F′ (AW1 at p = 5): an ordinary R = T theorem over a CM field. Khare–Thorne prove it conditionally. Its inputs are now largely known, but the combination has not been checked in our setting.
- Step C, classicality at the Artin weight (AW2 at p = 5): open, and no method is known. This is the same gap as at p = 2, now at an odd prime.

| Step | Statement | Label |
| --- | --- | --- |
| A | ρ̄₅ ⊗ φ restricted to F′ is modular, from a weight-2 cuspidal form | \[T\], explicit curve A with an exact certificate (section 2); Lemma 2.2 no longer needed |
| B | ρ restricted to F′ is a point of Hida's ordinary Hecke algebra at p = 5 | \[S\], needs a new R = T theorem; Khare–Thorne 6.29 does not apply as stated (section 4) |
| C | that point is a classical form of Artin weight | open |
| D | descent from F′ to ℚ | \[T\], cyclic base change (F′/ℚ biquadratic) |

Labels: \[T\] proved (here or in a cited source), \[S\] a strategy with a precise statement, \[C\] supported by computation. Nothing here proves Artin's conjecture for ρ.

## 1. Setting and notation

- ρ: G\_ℚ → GL₂(ℂ) is even icosahedral of conductor 1951, with det ρ = χ of order 5, χ(n) = ζ₅^(2 log₃ n) mod 1951, tr ρ(Frob\_p) = χ(p)³ t\_p, t\_p ∈ ℤ\[(1+√5)/2\], and ρ(c) = −I. K is the A₅-field cut out by the projective representation.
- Frobenius classes in A₅ (data/classes\_1951.json): Frob₂ in 3A, Frob₃ in 5B, Frob₅ in 2A.
- ρ = ρ₀ ⊗ χ³ with ρ₀ of image 2A₅ and determinant 1. ρ₀ is realized over ℚ(ζ₅), which splits the icosian quaternion algebra over ℚ(√5) (ramified only at the two real places). So ρ is realized over ℚ(ζ₅).
- λ = (1 − ζ₅), with residue field F₅. Let ρ̄₅ = ρ mod λ. Since χ ≡ 1 mod λ, ρ̄₅ = ρ̄₀: its image is SL₂(F₅) and its determinant is 1. Reduction mod λ is injective on 2A₅ (the only normal subgroups are 1, {±I}, 2A₅, and −I ↦ −I), so 2A₅ ≅ SL₂(F₅).
- F′ = ℚ(i, √5), defined by y⁴ − 8y² + 36 (discriminant 400). It is CM with F′⁺ = ℚ(√5), and ζ₅ ∉ F′. Above 5 there are two primes, each with e = 2 and f = 1; above 1951 there are two primes with f = 2. K ∩ F′ = ℚ, because A₅ is perfect.
- ε̄₅ is the mod-5 cyclotomic character. On G\_F′ it has order 2 and cuts out F′(ζ₅) = F′(√δ), δ = (5 + √5)/2, since (ζ₅ − ζ₅⁻¹)² = −δ and −1 is a square in F′.
- φ: G\_F′ → F₅ˣ is a character with φ² = ε̄₅ on G\_F′ (Lemma 2.1).

## 2. Theorem A: residual modularity over F′

**Theorem A.** There is an elliptic curve A/F′ with A\[5\] ≅ ρ̄₅ ⊗ φ as G\_F′-modules, and every such A is modular. Hence ρ̄₅ restricted to G\_F′ is, up to the twist by φ, the mod-5 representation of a cuspidal cohomological automorphic representation π of GL₂(𝔸\_F′) of parallel weight 2. \[T\]

**Lemma 2.1 (the twist φ).** There is φ: G\_F′ → F₅ˣ with φ² = ε̄₅ on G\_F′. It can be chosen unramified at any finite set of primes not above 2 or 5.

*Proof.* F′(√δ)/F′ embeds in a cyclic quartic extension M/F′ if and only if the quaternion algebra (δ, −1) over F′ is split. Since −1 = i², it is. Identify Gal(M/F′) ≅ ℤ/4 ≅ F₅ˣ and let φ be the resulting character. Then φ² is the quadratic character with kernel F′(√δ), which is ε̄₅ on G\_F′. At a prime v ∤ 10 the restriction of φ to inertia is quadratic, so a global quadratic twist (Grunwald–Wang, no obstruction in exponent 2) makes φ unramified at finitely many chosen v. ∎

**Lemma 2.2 (the twisted X(5) is P¹).** Let F be a field of characteristic 0 and r̄: G\_F → GL₂(F₅) with det r̄ = ε̄₅. Then the curve X\_r̄ classifying pairs (E, ι: E\[5\] ≅ r̄), with ι symplectic for the Weil pairing and the identification Λ²r̄ ≅ μ₅ given by det, is isomorphic to P¹ over F. In particular X\_r̄(F) is infinite, and away from the 12 cusps its points give elliptic curves A/F with A\[5\] ≅ r̄. Local conditions at finitely many places can be imposed (weak approximation on P¹).

*Proof.* Over F̄, X\_r̄ is X(5): smooth, projective, geometrically connected, of genus 0, with 12 cusps. Full level 5 is rigid (−1 acts by −1 on E\[5\]), so by Deligne–Rapoport the universal generalized elliptic curve and its Hodge bundle ω descend to F. Kodaira–Spencer gives ω² ≅ Ω¹(cusps), of degree 2g − 2 + 12 = 10, so deg ω = 5 (equivalently, dim M₁(Γ(5)) = 6). A genus-0 curve over F with a line bundle L of odd degree 2m + 1 has the degree-1 bundle L ⊗ Ω¹^m, hence a rational point by Riemann–Roch, hence is P¹. ∎

The same argument gives P¹ for p = 3 (deg ω = 1) and fails for p ≥ 7 (genus > 0). The Fernández–Lario–Rio disjointness condition concerns twists built from a projective representation, not this linear one. Lemma 2.2 is my own proof, and probably the argument Shepherd-Barron–Taylor use. An expert should check it before it is relied on.

*Proof of Theorem A.* Put r̄ = ρ̄₅ ⊗ φ on G\_F′; then det r̄ = φ² = ε̄₅. Lemma 2.2 gives A. Caraiani–Newton Theorem 6.1 proves A modular if F′ is imaginary CM with ζ₅ ∉ F′, r̄ restricted to G\_F′(ζ₅) is absolutely irreducible, and r̄ is decomposed generic. Each holds:

| Hypothesis | Why it holds | Checked |
| --- | --- | --- |
| F′ imaginary CM, ζ₅ ∉ F′ | ℚ(ζ₅) is cyclic quartic, F′ is biquadratic | PARI: Φ₅ has no root in F′ |
| absolutely irreducible on G\_F′(ζ₅) | F′(ζ₅) is abelian over ℚ, so disjoint from K; the image stays SL₂(F₅), irreducible on F₅² | from A₅ perfect |
| decomposed generic | ℓ = 89 splits completely in F′ (4 primes), Frob₈₉ in 3A: eigenvalue ratio of order 3, not in F₅, so ≠ 89 mod 5; φ unramified at 89 by Lemma 2.1 | PARI + classes\_1951.json; 101 (class 2A, ratio −1 ≠ 1) also works |

So A is modular, and π = π\_A satisfies r̄\_π ≅ A\[5\] (up to the usual dual twist) ≅ ρ̄₅ ⊗ φ. ∎

**An explicit A, with an exact certificate (19 November).** Theorem A no longer depends on Lemma 2.2.

1. Let J ∈ F′ be a root of the explicit integer quartic in outputs/galois1951/p5route/j18.txt (its field is F′), and let A be the elliptic curve with j = 1728 J. Here j ≠ 0, 1728.
2. Let K₆ be the field of x⁶ − 75x⁴ − 70x³ + 826x² − 210x − 625, Cayley's sextic resolvent of f₅, which is the D₅-fixed field of the A₅-field K. Let L = K₆F′, of degree 24.
3. PARI finds t₀ ∈ L with (t₀² + 10t₀ + 5)³ = j t₀, checked exactly in L. Its characteristic polynomial over ℚ is squarefree of degree 24, so F′(t₀) = L. The relation j = (t² + 10t + 5)³/t is Fricke's X₀(5); checked on 11a1 (two roots), 11a3 (one) and 37a1 (none).
4. So the G\_F′-set of cyclic 5-subgroups of A has point stabilizer field K₆F′, the same as the 6-point set of the projective ρ̄₅. The two permutation representations are conjugate in S₆. The normalizer of the transitive A₅ in S₆ is PGL₂(F₅), so projective A\[5\] ≅ projective ρ̄₅, and A\[5\] ≅ ρ̄₅ ⊗ φ′ with φ′ F₅ˣ-valued and φ′² = ε̄₅.
5. Caraiani–Newton 6.1 then applies to A: ζ₅ ∉ F′; the image on G\_F′(ζ₅) is irreducible; and A has good reduction at every prime over 89 (class 3A), so A\[5\] is decomposed generic. A is modular. \[T\]

The same curve has potentially good ordinary reduction at both v | 5 (section 7), which supplies input B0.

## 3. Local data at 5, and the weight Step B needs

**Proposition 3.1.** At each of the two primes v | 5 of F′, ρ restricted to G\_F′ᵥ is ψ₁ ⊕ ψ₂ with ψ₁, ψ₂ unramified and ψ̄₁ ≠ ψ̄₂: ordinary and 5-distinguished. \[T\]

*Proof.* F′ᵥ = ℚ₅(√5) has residue field F₅, so Frobᵥ restricts to Frob₅, in class 2A. ρ(Frob₅) has eigenvalues α and −α (trace 0), and 2α ≢ 0 mod λ. ρ is unramified at 5. ∎

This gives four refinements (a choice of Uᵥ-eigenvalue ±α at each v | 5), the analogue of the mixed and pure refinements at v, v̄ | 2 over ℚ(√−7). The choice of field matters: over ℚ(√−7), 5 is inert, Frobᵥ = Frob₅² is scalar, and ρ is not 5-distinguished. That is why the route goes through ℚ(i).

**The weight issue.** ε̄₅ is ramified on G\_F′ᵥ, because ℚ₅(ζ₅)/ℚ₅(√5) is totally ramified. So φ is ramified at v, and A\[5\] ≅ ρ̄₅ ⊗ φ has no unramified quotient at v: π\_A cannot be ordinary with trivial nebentypus at v. It can at best be ordinary up to a ramified character (potentially ordinary A). An ordinary lift of ρ̄₅ restricted to G\_F′ᵥ of shape ψ̃₁ ⊕ ψ̃₂ ε^(k−1) needs ε̄₅^(k−1) trivial on G\_F′ᵥ, so k odd. That means parallel weight 3 (coefficients Sym¹ ⊗ Sym¹ at each complex place), or weight 2 with a quadratic nebentypus at v. This is the same reason the 2-adic test used V₃,₃.

So Step B needs ρ̄₅ to be ordinarily automorphic over F′: residually modular by a form that is ordinary at both v | 5, in weight 3 or with that nebentypus. Theorem A supplies a non-ordinary weight-2 form. Passing from one to the other is a change of weight. In the literature it is done by Hida theory plus potential-automorphy arguments (Allen–Calegari–Caraiani–Gee–Helm–Le Hung–Newton–Scholze–Taylor–Thorne), possibly after a further solvable CM base change, which is harmless for the descent. To check: input B0 in section 4.

**A shortcut for B0 (to test, E1 in section 7).** Ordinary-with-character is enough, and it may be arranged inside Theorem A. If A has potentially good ordinary reduction at v, with inertia acting on the étale quotient of A\[5\] by η, then A\[5\] restricted to Iᵥ is (ε̄₅η⁻¹, η). We need both characters to equal φᵥ, so η = φᵥ, and the condition ε̄₅φᵥ⁻¹ = φᵥ is exactly φ² = ε̄₅. Here φᵥ has order 4 on inertia, so A is a quartic twist of a curve with good ordinary reduction and automorphisms μ₄: reduction j = 1728, ordinary because 5 ≡ 1 mod 4. Lemma 2.2 allows weak approximation, so B0 reduces to one local question: does X\_r̄ have F′ᵥ-points over j = 1728 (of the right inertia type) at both v | 5? That is a finite computation.

## 4. Step B: 5-adic automorphy (AW1 at p = 5)

**Target statement B.** Let 𝕋^ord be Hida's ordinary Hecke algebra for GL₂ over F′ at tame level 1951 (character χ composed with the norm), localized at the maximal ideal 𝔪 of ρ̄₅. Then ρ restricted to G\_F′, with a chosen refinement at each v | 5, defines a point x of Spec 𝕋^ord\_𝔪 over Q̄₅ at the Artin weight. That is, x(T\_w) = tr ρ(Frob\_w) for all primes w ∤ 5 · 1951 and x(Uᵥ) = the chosen root ±α. \[S\]

The mechanism: ρ restricted to G\_F′ is a Q̄₅-point of the ordinary deformation ring R^ord of ρ̄₅ (Proposition 3.1 gives the ordinary condition at v | 5; at 1951 the deformation is minimal). An isomorphism R^ord\_red ≅ 𝕋^ord\_𝔪, or a surjection with nilpotent kernel, carries that point to 𝕋^ord. Khare–Thorne prove such an R = T theorem (their Theorem 6.29) over CM fields, conditionally on their Conjectures 6.18 and 6.27.

| Input | Content | Status |
| --- | --- | --- |
| B0 | ρ̄₅ is ordinarily automorphic over F′ (section 3) | done: the certified curve A of section 2 has potentially good ordinary reduction (type III) at both primes over 5, so π\_A is ordinary up to a character there; check against Khare–Thorne's exact definition |
| B1 | Galois representations with coefficients in 𝕋^ord (KT Conjecture 6.18) | Scholze, up to a nilpotent ideal of bounded exponent; check that it suffices in the Λ-adic form |
| B2 | ordinary local–global compatibility at the primes over 5 (part of KT Conjecture 6.27) | Caraiani–Newton; A'Campo–Hevesi–Thorne–Whitmore 2026; check torsion and Λ-adic versions |
| B3 | local–global compatibility at Taylor–Wiles primes (rest of 6.27) | proved by Allen–Calegari–Caraiani–Gee–Helm–Le Hung–Newton–Scholze–Taylor–Thorne |
| B4 | "enormous" residual image: ρ̄₅ on G\_F′(ζ₅) has image SL₂(F₅) | fails at p = 5 (H¹(SL₂(F₅), ad⁰) ≠ 0); Caraiani–Newton's device at fixed weight; see the E3 findings below |

**E3 findings (19 November): Khare–Thorne 6.29 does not apply as stated.** Its standing assumptions (their section 6.7) are designed for their Leopoldt application. Ours differ at three points:

| KT assumption | Our ρ̄₅ over F′ | Consequence |
| --- | --- | --- |
| ρ̄ unramified outside the primes over p | ramified at 1951: inertia has order 5, which mod 5 becomes a nontrivial unipotent (1951 ≡ 1 mod 5) | the local deformation ring at 1951 has several components (ρ is of principal-series type, residually unipotent); needs Taylor's Ihara avoidance |
| ρ̄ trivial at each prime over p, and local degree \[F\_v : ℚ\_p\] > 1 + n(n−1)/2 = 2 | at each prime over 5, ρ̄ is ψ̄₁ ⊕ ψ̄₂ with ψ̄₁ ≠ ψ̄₂, and the local degree is 2 | the distinguished case has a smooth ordinary local ring, so it should be easier, but it is a different theorem |
| Frob\_a scalar for an auxiliary prime a | arrangeable (a over 4229, split completely in K F′) | none |

All three can be met after a solvable base change to a CM field F″ of degree 80; only the image condition remains. See the companion note "Target theorem for Step B", section 4.

The image condition B4 is also delicate. For p = 5, ad⁰ = Sym² = Sym^(p−3), and H¹(SL₂(F₅), Sym²) ≅ F₅ ≠ 0: SL₂(F₅) is the known exception to adequacy at p = 5. Caraiani–Newton 6.1 overcomes this in fixed regular weight using only decomposed generic and irreducibility on G\_F(ζ₅). A Λ-adic version must use the same device.

Verdict: Step B needs a new theorem. It would be an ordinary Λ-adic R = T for GL₂ over a CM field, with distinguished residual representation at p, Ihara avoidance at a prime ℓ ≡ 1 mod p with unipotent residual inertia, and residual image SL₂(F₅) at p = 5. It would combine Khare–Thorne's Λ-adic framework with Caraiani–Newton's treatment at p = 5. That is a substantial research project, not a citation. \[S\] The Λ-adic part of 6.29 also assumes the Calegari–Geraghty vanishing (CG), known only for large p with p unramified (Gholami 2022), not at p = 5 here. See the note "Target theorem for Step B", section 5.

With such a theorem (and B1–B3 in their Λ-adic forms), B would be a theorem. It is the theorem-level version of what the 2-adic test measures: there we found eigen-lifts of tr ρ mod 2³ and not mod 2⁴ at weight 3 over ℚ(√−7), matching the bound v₂(t₃) = 3. At p = 2, neither the residual input nor the R = T theorem is available, so B cannot be proved there. That asymmetry is the main reason to work at 5.

## 5. Step C: classicality at the Artin weight (AW2 at p = 5), the open core

**What C asks.** C asks that the point x of Step B come from a cuspidal π of GL₂(𝔸\_F′) whose two archimedean components are the unitary principal series at spectral parameter 0. That is the Laplace eigenvalue 1 on hyperbolic 3-space, the analogue of 1/4 on the upper half-plane. Such π are not cohomological: they occur in no H^i(Y\_K, V) for any level K and any algebraic local system V. With Step D (cyclic descent along F′/ℚ(i)/ℚ), C for F′ is equivalent to Artin's conjecture for ρ.

**Why no current method reaches it.** Over ℚ, Artin-weight (weight one) forms live in the coherent cohomology of modular curves. Buzzard–Taylor, Calegari–Geraghty and Pan all work there. Over a CM field, GL₂ has no Shimura variety and no coherent model. So the form must be produced as an L² automorphic form from a point of ordinary completed cohomology, and no theorem does this for any non-cohomological case over a CM field.

**Approaches, in order of promise (all \[S\]):**

1. U(2,2) boundary. Scholze realizes GL₂ over a CM field in the Borel–Serre boundary of U(2,2) Shimura varieties, which do have coherent cohomology. Plan: realize x as the constant term of an irregular-weight coherent class on U(2,2), using Pan-type geometric Sen theory there, then recover π from the constant term. Gap: no theorem identifies boundary contributions of irregular coherent classes.
2. Derived Hecke structure. With ℓ₀ = \[F′:ℚ\]/2 = 2, the R = T of Step B is "derived" (Calegari–Geraghty, Venkatesh). The Artin point needs an analytic incarnation of the derived action; none is known.
3. Spectral detection. Count the spectrum at parameter 0 with a pole of L(s, Sym¹²) (Klein's degree-12 invariant), beyond endoscopy style. This is out of reach.

**What p = 5 changes and what it does not.** It gives a proved residual input (A), a field where ρ is ordinary and distinguished at p (Proposition 3.1), and an R = T theorem within reach (B). It does not change C: the classicality mechanism is missing at every prime.

## 6. Relation to the 2-adic results

The 2-adic computations are numerical evidence for the p = 2 analogue of Step B. They say nothing about Step C.

| Result | Where | Label | Analogue at p = 5 |
| --- | --- | --- | --- |
| eigen-lifts of tr ρ mod 8, not mod 16, at all four refinements (weight 3, level 1951, 13 operators; 65.5 h, kernels certified) | ℚ(√−7) | \[T\] computation; control run pending | Step B |
| exactly one mod-2 class with the ρ̄ eigenvalues at 48 operators, both refinements at (1+i); controls 0 | ℚ(i) | \[T\] computation, \[C\] residual modularity mod 2 | Theorem A (proved at 5) |
| no classical holomorphic form is congruent to ρ mod 4 (parity wall) | ℚ | \[T\] | same wall: why the base field must be CM |

The ordinary bound v₂(t₃) = 3 was reached exactly at every refinement. At p = 5 the same mechanism gives depth at most v₅(t\_k) = 1 + v₅(k − 1) along weights k ≡ 1 mod 4: depth 1 at k = 5, and depth 2 only from k = 21 (coefficients Sym¹⁹ ⊗ Sym¹⁹, dimension 20² = 400). So depth measurements at 5 are not feasible, and p = 2 stays the numerical window while p = 5 is the theoretical one.

## 7. Experiments and checks, in order

- [ ] E1 (done, see below). Construct A explicitly. Reduce the A₅ quintic of K to Brioschi form over F′ (Klein's icosahedral resolvent; the accessory square root is rational over F′ by Lemma 2.2), read off j(A), and verify a\_w(A) ≡ tr(ρ̄₅ ⊗ φ)(Frob\_w) mod 5 at many primes w. Then search the P¹ of Lemma 2.2 for an A that is potentially ordinary at both v | 5 with reduction j = 1728, which settles B0.
- [ ] E2. Independent check of Lemma 2.2: by an expert, or against the Shepherd-Barron–Taylor text if it becomes available. E1 also checks it in practice.
- [ ] E3 (first pass done, see section 4: Khare–Thorne 6.29 does not apply as stated). Check inputs B1–B4 against the exact statements: Khare–Thorne section 6, Caraiani–Newton on ordinary local–global compatibility, A'Campo–Hevesi–Thorne–Whitmore 2026, and the definition of an enormous image at p = 5.
- [ ] E4. The 1951 control run (q11 shifted by 2; expected depth 1). This is needed before the 2-adic depth result counts.
- [ ] E5. Write Step C as a precise conjecture on F′ (a classicality statement for ordinary points of non-cohomological weight). Then test it on the even tetrahedral case of conductor 163, which is known to be automorphic: there the classical Bianchi form exists, so the conjecture must hold.

**E1 results (19 November).** The construction of Lemma 2.2 runs explicitly and gives elliptic curves over F′ whose 5-torsion matches ρ̄₅ at every prime tested.

1. An isotropic trace-zero y in K₅ ⊗ ℚ(i) for q(y) = Tr(y²) exists already over ℚ(i) (qfsolve; det q = 2² · 5⁷ · 7² · 71² · 137² · 1951⁴).
2. Klein's binary icosahedral group, computed exactly over ℚ(ζ₅), writes y as a rank-1 tensor v ⊗ w. Klein's invariant J at v satisfies a quartic over ℚ with 596-digit coefficients, stable from 2200 to 5200 digits (residual 10⁻⁴⁶⁰⁶). Its field is x⁴ + 3x² + 1, which is F′. \[N\]
3. For E with j = 1728 J: a\_w(E)² ≡ N(w) · tr ρ̄₅(Frob\_w)² mod 5 at all good primes w below 3000. Curves with j perturbed fail at about 60% of primes. \[T\] as a computation; \[C\] that E\[5\] ≅ ρ̄₅ ⊗ φ.

| Sample point | Primes passing | j at the two primes v over 5 | Reduction at v |
| --- | --- | --- | --- |
| first (y over ℚ(i), seed 0) | 1026 of 1026 | v(j) = 8, j ≡ 0 | potentially supersingular |
| seeds 11–17 (7 points) | not run | v(j) ≥ 8, j ≡ 0 | potentially supersingular |
| seed 18 | 1024 of 1024 | v(j) = 0, j ≡ 1728 mod v, v(j − 1728) = 5 | Kodaira III, conductor exponent 2: potentially good ordinary |

The dichotomy is forced: inertia at v acts on A\[5\] by the order-4 scalar φᵥ, so j reduces to 0 or 1728 at each v. The seed-18 curve is the B0 candidate of section 3. The exact field identity is now done: see "An explicit A, with an exact certificate" in section 2. Files: outputs/galois1951/p5route.

Not planned: mod-5 depth measurements. The first informative weight is 21, and the minimal Serre weight of ρ̄₅ over ℚ(i) is already (5, 5), with a 16-dimensional coefficient system.

## Sources

- [Caraiani–Newton, Modularity of elliptic curves over imaginary quadratic fields](https://arxiv.org/abs/2301.10509): Theorem 6.1, used in Theorem A.
- [Allen–Khare–Thorne, Modularity of GL₂(F\_p)-representations over CM fields](https://arxiv.org/pdf/1910.12986): residual input inside Caraiani–Newton.
- [Khare–Thorne, Potential automorphy and the Leopoldt conjecture](https://arxiv.org/abs/1409.7007): Theorem 6.29 and Conjectures 6.18, 6.27, used in Step B.
- [Scholze, On torsion in the cohomology of locally symmetric varieties](https://www.math.uni-bonn.de/people/scholze/Torsion.pdf): Corollary V.4.3, Remark V.4.6, input B1.
- [A'Campo–Hevesi–Thorne–Whitmore, local–global compatibility over CM fields at p (2026)](https://arxiv.org/pdf/2607.11763): input B2.
- [Fernández–Lario–Rio, On twists of the modular curves X(p)](https://cambridge.org/core/journals/bulletin-of-the-london-mathematical-society/article/on-twists-of-the-modular-curves-xp/71FA5FBABA5E3E86813A939512990442): the disjointness condition discussed after Lemma 2.2.
- Shepherd-Barron–Taylor, Mod 2 and mod 5 icosahedral representations, JAMS 10 (1997), doi 10.1090/S0894-0347-97-00226-9: not read; no longer needed if Lemma 2.2 holds.
- Computations (PARI, this project): F′ data, ζ₅ ∉ F′, primes above 5 and 1951, decomposed-generic witnesses 89 and 101, Frobenius classes from data/classes\_1951.json.
