# Target theorem for Step B: Λ-adic ordinary R = T for ρ̄₅ over ℚ(i, √5)

Nov 19, 2026 · Dula

This note states the one automorphy lifting theorem that the p = 5 route to Artin's conjecture for the even icosahedral ρ of conductor 1951 needs and does not have. Every hypothesis is instantiated by explicit data that has already been computed or proved.

The theorem, B∗, is an ordinary R = T for GL₂ over a CM field, in Hida families (Λ-adic). It would make ρ restricted to F′ = ℚ(i, √5) a point of Hida's ordinary Hecke algebra at the Artin weight: 5-adic automorphy, AW1 at p = 5. It would not give Artin's conjecture. That also needs classicality at the Artin weight (Step C), which is open and is not addressed here.

The residual input is proved: ρ̄₅ restricted to F′ is modular, twisted by a character, through an explicit elliptic curve with an exact certificate ("The p = 5 route for ρ₁₉₅₁", Theorem A).

## 1. The target theorem B∗

**Setting.** F is an imaginary CM field, p an odd prime, and O the ring of integers of a finite extension of ℚ\_p, with residue field k. S is a finite set of finite places of F, stable under complex conjugation, containing the set S\_p of places above p. Λ = O\[\[T\_p\]\], where T\_p is the pro-p part of ∏\_{v | p} T(O\_Fᵥ), with T the diagonal torus of GL₂. Let ρ̄: G\_F,S → GL₂(k) be continuous and absolutely irreducible.

**Hypotheses.**

1. H1, ordinarily automorphic. There is a regular algebraic cuspidal π on GL₂(𝔸\_F) with r̄\_ι(π) ≅ ρ̄, which is ι-ordinary at every v | p up to a finite-order character of O\_Fᵥˣ. That is, πᵥ is a constituent of Ind(μ₁, μ₂) with μ₁ an ι-adic unit on a uniformizer, and nebentypus at v allowed.
2. H2, image. ζ\_p ∉ F; ρ̄ restricted to G\_F(ζ\_p) is absolutely irreducible; ρ̄ is decomposed generic. No adequacy or enormousness is assumed, which allows image SL₂(F₅) at p = 5, where H¹(SL₂(F₅), ad⁰) ≅ F₅.
3. H3, distinguished at p. For each v | p, ρ̄ restricted to G\_Fᵥ is an extension of ψ̄ᵥ,₂ by ψ̄ᵥ,₁ with ψ̄ᵥ,₁ ≠ ψ̄ᵥ,₂ (in our case split). No condition on \[Fᵥ : ℚ\_p\] and no triviality of ρ̄ at v.
4. H4, ramification away from p. For each v ∈ S ∖ S\_p, either ρ̄ is minimally ramified at v, or N(v) ≡ 1 mod p and ρ̄ restricted to Iᵥ is a nontrivial unipotent. In the second case the local condition is the union of the unipotent (Steinberg) component and the tame principal-series component with characters of p-power order, as in Taylor's Ihara avoidance.
5. H5, neat level. There is an auxiliary place a ∉ S as in Khare–Thorne section 6.7 that makes the level neat.
6. H6, Galois representations. Khare–Thorne Conjectures 6.18 and 6.27 hold for the ordinary Hecke algebras involved: Galois representations with coefficients in 𝕋^ord (up to a nilpotent ideal of bounded exponent), with local–global compatibility at S\_p and at Taylor–Wiles places.

**Objects.** R^ord is the Λ-algebra pro-representing deformations ρ of ρ̄, unramified outside S, with three conditions. At v | p, ρ restricted to G\_Fᵥ is an extension (χᵥ,₁ ∗; 0 χᵥ,₂) lifting the chosen ordered pair (ψ̄ᵥ,₁, ψ̄ᵥ,₂), with χᵥ,ᵢ on inertia given by the universal Λ-character. At v ∈ S ∖ S\_p, the H4 condition holds. The determinant is fixed up to the Λ-variation. 𝕋^ord\_𝔪 is the Hecke algebra on Hida's ordinary part of the completed cohomology of the GL₂ locally symmetric spaces over F, in all degrees. Its level is Iwahori at p and of Γ₁-type at S ∖ S\_p, enough to see the principal-series characters. It is localized at the non-Eisenstein maximal ideal 𝔪 of ρ̄.

**Conclusion of B∗.** The natural map R^ord → 𝕋^ord\_𝔪 is surjective with nilpotent kernel. Equivalently: every continuous lift ρ: G\_F → GL₂(Q̄\_p) of ρ̄ of this type defines a Q̄\_p-point of 𝕋^ord\_𝔪. Its Frobenius traces are then a system of Hecke eigenvalues in ordinary completed cohomology, at whatever point of weight space its Hodge–Tate data give, classical or not.

## 2. Instantiation for ρ̄₅ over F′

All entries below are proved or computed, except where the last column says otherwise.

| Item | Our data | Status |
| --- | --- | --- |
| F | F′ = ℚ(i, √5), y⁴ − 8y² + 36, discriminant 400; F⁺ = ℚ(√5) | \[T\] |
| p, O, k | p = 5; O = ℤ₅\[ζ₅\] with λ = (1 − ζ₅); k = F₅ | \[T\] |
| ρ̄ | ρ mod λ restricted to G\_F′, image SL₂(F₅), determinant 1; twist φ′ with φ′² = ε̄₅ relates it to A\[5\] | \[T\] |
| S | the two primes over 5 (e = 2, f = 1); the two primes over 1951 (f = 2); the primes over 2 (F′/F⁺ is ramified there; ρ̄ is unramified) | \[T\] |
| H1 | π = π\_A ⊗ φ′⁻¹, A the certified curve (j = 1728 J, J in p5route/j18.txt); A has potentially good ordinary reduction, Kodaira III, at both primes over 5 | \[T\]; match with the precise ι-ordinary notion to confirm |
| H2 | ζ₅ ∉ F′; image SL₂(F₅) on G\_F′(ζ₅) since F′(ζ₅) is abelian over ℚ; decomposed generic at ℓ = 89 (splits completely, Frobenius class 3A, eigenvalue ratio of order 3, not in F₅) | \[T\] |
| H3 | at each prime over 5, ρ̄ is ψ̄₁ ⊕ ψ̄₂ unramified, Frobenius ↦ α, −α (Frob₅ in class 2A); four choices of ordered pairs; local degree 2 | \[T\] |
| H4 | at each prime over 1951, N(v) = 1951² ≡ 1 mod 5; ρ̄ on inertia is a nontrivial unipotent (an order-5 element of SL₂(F₅)); ρ on inertia is 1 ⊕ χ with χ of order 5: the tame principal-series component | \[T\] |
| H5 | a = a prime over 4229: 4229 ≡ 9 mod 20 splits completely in F′, Frobenius class trivial in A₅ (so ρ̄(Frob\_a) = ±I), N(a) ≢ 1 mod 5 | \[T\] |
| H6 | Scholze (Galois representations); Caraiani–Newton and A'Campo–Hevesi–Thorne–Whitmore (local–global compatibility at p); Allen et al. (Taylor–Wiles places) | known at fixed weight; Λ-adic forms to check |
| the lift ρ | ρ restricted to G\_F′, valued in GL₂(O): unramified at 5, ordinary with the chosen refinement, of type H4 at 1951, Hodge–Tate weights (0, 0) at both embeddings (the Artin weight) | \[T\] |

## 3. What B∗ gives, and what it does not

**Corollary (Step B, AW1 at p = 5).** Assume B∗ with the data of section 2. For each of the four refinements, ρ restricted to G\_F′ defines a point x of Spec 𝕋^ord\_𝔪 at the Artin weight. There, x(T\_w) = tr ρ(Frob\_w) for every prime w of F′ outside S ∪ {a}, and x(Uᵥ) = the chosen root ±α at each v over 5.

This is the 5-adic counterpart of the 2-adic computation. At p = 2 over ℚ(√−7), the eigensystem of tr ρ lifts mod 8 and not mod 16 at all four refinements (weight 3, level 1951), exactly the bound allowed at that weight. That is numerical evidence for the same statement at p = 2, where neither the residual input nor an R = T theorem is available.

**What it does not give.** The Artin weight is not cohomological, so x is a Hecke eigensystem in ordinary completed cohomology that occurs in no finite-level cohomology with algebraic coefficients. Turning x into a cuspidal automorphic representation, with the principal series at spectral parameter 0 at both complex places, is Step C. No current method does this over a CM field. With Step C, cyclic descent along F′/ℚ(i)/ℚ would give Artin's conjecture for ρ.

## 4. What is known, what is new, and a simplification

| Ingredient | Known | New in B∗ |
| --- | --- | --- |
| ordinary lifting over CM, fixed regular weight | Allen et al. (enormous image); Caraiani–Newton at p = 5 with image SL₂(F₅), assuming only decomposed generic and irreducibility on G\_F(ζ₅) | none |
| ordinary R = T in Hida families over CM | Khare–Thorne 6.29, under H6, with ρ̄ unramified outside p, trivial at each prime over p with local degree > 2, and enormous image | H2 in place of enormous image (needed at p = 5); H3 and H4 in place of triviality at p and unramified outside p |
| Ihara avoidance at ℓ ≡ 1 mod p | Taylor; used at fixed weight over CM by Allen et al. | in Λ-adic Calegari–Geraghty patching |
| H6 in Λ-adic form | Scholze's nilpotent ideal has exponent bounded uniformly in the level, as patching needs; local–global compatibility at p at fixed weight | uniform Λ-adic statements |
| H1, ordinary up to a character | potentially good ordinary curves give nearly ordinary forms with nebentypus | check against the definition used in the patching |

**A simplification by solvable base change.** Two of the three new points disappear over a larger field. Let F″ = F′ · M · C, where M is the cyclic quintic subfield of ℚ(ζ₁₉₅₁) (ramified only at 1951, and 1951 ≡ 1 mod 5), and C is the cyclic quartic CM subfield of ℚ(ζ₁₃) (5 has order 4 mod 13, so 5 is inert in C).

- F″ is abelian over ℚ, CM, of degree 80, and contains ℚ(i). ζ₅ ∉ F″, since F″ has ramification index 2 at 5 and ℚ(ζ₅) has 4.
- At 1951, F″ has ramification index 5, which kills the order-5 unipotent inertia of ρ̄. So ρ̄ restricted to G\_F″ is unramified outside 5, and ρ restricted to G\_F″ is unramified at 1951 as well.
- At each prime over 5, the residue degree is a multiple of 4. So Frobᵥ is a power of Frob₅⁴, which acts trivially through ρ̄ (an element of order 4 in SL₂(F₅)). Thus ρ̄ is trivial on G\_F″ᵥ, and the local degree is at least 8 > 2.
- The image on G\_F″(ζ₅) is still SL₂(F₅), because F″(ζ₅) is abelian over ℚ. A decomposed-generic prime exists by Chebotarev in K · F″.
- Residual ordinary automorphy over F″ follows from H1 over F′ by cyclic base change. Automorphy over F″ descends to ℚ along this solvable extension.

Over F″, Khare–Thorne's standing assumptions hold except one: enormous image fails, because H¹(SL₂(F₅), ad⁰) ≠ 0.

**The question for experts, in one line.** Does Khare–Thorne's Theorem 6.29 remain true at p = 5 when "enormous image" is replaced by "decomposed generic and absolutely irreducible on G\_F(ζ₅)", the device Caraiani–Newton use at fixed weight? A yes, with H6 in Λ-adic form, gives Step B for ρ₁₉₅₁. Section 5 below checks the remaining hypotheses of 6.29 and adds a second, harder point: the vanishing hypothesis (CG).

## 5. The rest of Theorem 6.29 (read 19 November)

The Λ-adic conclusion of 6.29 is part 1, "R acts nearly faithfully on H∗(F•\_𝔪)". That is the part that reaches non-classical points such as the Artin weight. Part 2 avoids (CG), but only at a regular classical weight λ with non-zero characteristic-0 cohomology, which is not ours.

| Hypothesis of 6.29 | Over F″ (or F′) | Status |
| --- | --- | --- |
| Conjectures 6.18, 6.27 | H6 | known at fixed weight; Λ-adic form to check |
| ρ̄ totally odd | F″ is CM, so it has no real places | to confirm against KT's definition for CM fields |
| (CG): H\_i(X\_U, k)\_𝔪 = 0 for i outside \[q₀, q₀ + ℓ₀\] | not known at p = 5 | open; see below |
| Fᵥ contains no non-trivial p-th roots of unity (v over p) | ramification index 2 at 5, while ℚ₅(ζ₅) has 4 | \[T\] |
| p > n | 5 > 2 | \[T\] |
| a absolutely unramified and not split in F(ζ\_p) | a over 4229, and 4229 ≡ 4 mod 5 | \[T\] |
| k contains the eigenvalues of the image | take k = F₂₅ (order-3 elements have eigenvalues in F₂₅) | \[T\] |

**The vanishing hypothesis.** Gholami (2022) proves (CG) for GL₂ over a CM field F = F⁺F₀ when the residual image is very large. His hypotheses are p split in F₀, hyperspecial level at p (so p unramified in F), and p > 2d²(d + 1)(4 − 2w), with d = \[F⁺ : ℚ\]. For F′, d = 2, so this needs p > 96 at weight 0, and 5 ramifies in F′. For F″, d = 40. So (CG) at p = 5 is open for our fields, and it is a second gap, independent of the image condition.

**The expert question, revised.** Can the Λ-adic near-faithfulness of Khare–Thorne 6.29 be proved at p = 5 for ρ̄₅ over F″ (or F′)? That requires (a) replacing "enormous image" by "decomposed generic and irreducible on G\_F(ζ₅)", and (b) either proving the vanishing (CG) at p = 5 with p ramified in F, or replacing it by a derived argument that does not need it.

## Sources

- [Khare–Thorne, Potential automorphy and the Leopoldt conjecture](https://arxiv.org/abs/1409.7007): Theorem 6.29, Conjectures 6.18 and 6.27, standing assumptions of section 6.7.
- [Caraiani–Newton, Modularity of elliptic curves over imaginary quadratic fields](https://arxiv.org/abs/2301.10509): Theorem 6.1 (p = 5, image SL₂(F₅)).
- [Allen–Khare–Thorne, Modularity of GL₂(F\_p)-representations over CM fields](https://arxiv.org/pdf/1910.12986).
- [Scholze, On torsion in the cohomology of locally symmetric varieties](https://www.math.uni-bonn.de/people/scholze/Torsion.pdf): Corollary V.4.3, Theorem V.4.1 (uniform nilpotence bound).
- [A'Campo–Hevesi–Thorne–Whitmore, local–global compatibility over CM fields at p (2026)](https://arxiv.org/pdf/2607.11763).
  - [Gholami, Non-Eisenstein cohomology of locally symmetric spaces for GL₂ over a CM field](https://arxiv.org/pdf/2203.13747): the vanishing (CG) for large p.
- Companion doc "The p = 5 route for ρ₁₉₅₁" (Theorem A, the certified curve) and the project files in outputs/galois1951/p5route.
