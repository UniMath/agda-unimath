# Cavallo's trick

```agda
module synthetic-homotopy-theory.cavallos-trick where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sections
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import structured-types.h-spaces
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-sections
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
```

</details>

## Idea

{{#concept "Cavallo's trick" Agda=cavallos-trick}} is a way of upgrading an
unpointed [homotopy](foundation.homotopies.md) between
[pointed maps](structured-types.pointed-maps.md) to a
[pointed homotopy](structured-types.pointed-homotopies.md).

Originally, this trick was formulated by [Evan Cavallo](https://ecavallo.net/)
for homogeneous spaces, but it works as soon as the evaluation map
`(id ~ id) → Ω B` has a [section](foundation-core.sections.md). This
generalization was found by Buchholtz, Christensen, Rijke, and Taxerås Flaten,
and appears as Lemma 2.7 (2)⇒(3) in {{#cite BCFR23}}.

## Theorem

```agda
module _
  {l1 l2 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  (let a∗ = point-Pointed-Type A)
  (let b∗ = point-Pointed-Type B)
  where

  htpy-cavallos-trick :
    (f g : A →∗ B) → section (λ (H : id ~ id) → H b∗) →
    (map-pointed-map f ~ map-pointed-map g) →
    unpointed-htpy-pointed-map f g
  htpy-cavallos-trick (f , p) (g , q) (K , α) H x =
    K (inv q ∙ inv (H a∗) ∙ p) (f x) ∙ H x

  compute-htpy-cavallos-trick :
    (f g : A →∗ B) (s : section (λ (H : id ~ id) → H b∗)) →
    (H : map-pointed-map f ~ map-pointed-map g) →
    preserves-point-pointed-map f ∙
    inv (preserves-point-pointed-map g) ＝
    htpy-cavallos-trick f g s H a∗
  compute-htpy-cavallos-trick (f , refl) (g , q) (K , α) H =
    equational-reasoning
    inv q
    ＝ inv q ∙ inv (H a∗) ∙ H a∗
      by inv (is-section-inv-concat' (H a∗) (inv q))
    ＝ K (inv q ∙ inv (H a∗) ∙ refl) b∗ ∙ H a∗
      by
      right-whisker-concat
        ( inv (α (inv q ∙ inv (H a∗) ∙ refl) ∙ right-unit))
        ( H a∗)

  coherence-point-cavallos-trick :
    (f g : A →∗ B) (s : section (λ (H : id ~ id) → H b∗)) →
    (H : map-pointed-map f ~ map-pointed-map g) →
    coherence-point-unpointed-htpy-pointed-Π f g
      ( htpy-cavallos-trick f g s H)
  coherence-point-cavallos-trick (f , p) (g , q) (K , α) H =
    equational-reasoning
    p
    ＝ p ∙ inv q ∙ q
      by inv (is-section-inv-concat' q p)
    ＝ K (inv q ∙ inv (H a∗) ∙ p) (f a∗) ∙ H a∗ ∙ q
      by
      right-whisker-concat
        ( compute-htpy-cavallos-trick (f , p) (g , q) (K , α) H)
        ( q)

  cavallos-trick :
    (f g : A →∗ B) → section (λ (H : id ~ id) → H b∗) →
    (map-pointed-map f ~ map-pointed-map g) → f ~∗ g
  pr1 (cavallos-trick f g s H) = htpy-cavallos-trick f g s H
  pr2 (cavallos-trick f g s H) = coherence-point-cavallos-trick f g s H
```

## Corollaries

### Cavallo's trick for H-spaces

For pointed maps between H-spaces there is a map that promotes unpointed
homotopies to pointed ones.

First, we prove that the required evaluation map has a section. This is Lemma
2.7 (1)⇒(2) in {{#cite BCFR23}}.

```agda
module _
  {l : Level} (A : H-Space l)
  (let a∗ = unit-H-Space A)
  where

  pointed-section-Ω-ev-endo-H-Space :
    pointed-section (pointed-map-Ω (ev-endo-H-Space A))
  pointed-section-Ω-ev-endo-H-Space =
    pointed-section-Ω-pointed-section
      ( ev-endo-H-Space A)
      ( pointed-section-ev-endo-H-Space A)

  section-map-Ω-ev-endo-H-Space :
    section (map-Ω (ev-endo-H-Space A))
  section-map-Ω-ev-endo-H-Space =
    section-pointed-section
      ( pointed-map-Ω (ev-endo-H-Space A))
      ( pointed-section-Ω-ev-endo-H-Space)

  section-ev-unit-htpy-H-Space :
    section (λ (H : id ~ id) → H a∗)
  section-ev-unit-htpy-H-Space =
    section-left-factor (ev a∗) htpy-eq (section-map-Ω-ev-endo-H-Space)
```

```agda
module _
  {l1 l2 : Level}
  (A∗ : Pointed-Type l1) (B : H-Space l2)
  (let B∗ = pointed-type-H-Space B)
  where

  cavallos-trick-H-Space' :
    (f g : A∗ →∗ B∗) → (map-pointed-map f ~ map-pointed-map g) → f ~∗ g
  cavallos-trick-H-Space' f g =
    cavallos-trick f g (section-ev-unit-htpy-H-Space B)

module _
  {l1 l2 : Level}
  (A : H-Space l1) (B : H-Space l2)
  (let A∗ = pointed-type-H-Space A)
  (let B∗ = pointed-type-H-Space B)
  where

  cavallos-trick-H-Space :
    (f g : A∗ →∗ B∗) → (map-pointed-map f ~ map-pointed-map g) → f ~∗ g
  cavallos-trick-H-Space =
    cavallos-trick-H-Space' (pointed-type-H-Space A) B
```

## References

- Cavallo's trick was originally formalized in the
  [cubical agda library](https://agda.github.io/cubical/Cubical.Foundations.Pointed.Homogeneous.html).

{{#bibliography}}
