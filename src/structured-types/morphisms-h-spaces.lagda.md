# Morphisms of H-spaces

```agda
module structured-types.morphisms-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import group-theory.homomorphisms-semigroups

open import structured-types.h-spaces
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Consider two [H-spaces](structured-types.h-spaces.md) `X` and `Y`. A
{{#concept "morphism of H-spaces" Agda=hom-H-Space}} from `X` to `Y` consists of
a [pointed map](structured-types.pointed-maps.md) `f : X →∗ Y` that preserves
the unital binary operation

```text
  α : (x x' : X) → f (μ x x') ＝ μ (f x) (f x')
```

and which furthermore comes equipped with the following structure, witnessing
that the unit laws are preserved:

- For each `x' : X` an identification `α₁ x'` witnessing that the triangle

  ```text
                              α * x'
                  f (μ * x') -------> μ (f *) (f x')
                        \                 /
                         \               / ap (μ - (f x')) f₁
                          \             /
                           \           ∨
    ap f (left-unit-law x') \       μ * (f x')
                             \       /
                              \     / left-unit-law (f x')
                               \   /
                                ∨ ∨
                                f x'
  ```

  commutes.

- For each `x : X` an identification `α₂ x` witnessing that the triangle

  ```text
                              α x *
                  f (μ x *) --------> μ (f x) (f *)
                        \                 /
                         \               / ap (μ (f x) -) f₁
                          \             /
                           \           ∨
    ap f (right-unit-law x) \       μ (f x) *
                             \       /
                              \     / right-unit-law (f x)
                               \   /
                                ∨ ∨
                                f x
  ```

  commutes.

- An identification `α₃` witnessing that the square

  ```text
                                                     α₁
     α₀ * * ∙ (ap (μ - (f *)) f₁ ∙ left-unit-law *) ---> ap f (left-unit-law *)
                       |                                         |
         (α₀ * *) ·l β |                                         |
                       ∨                                         ∨
    α₀ * * ∙ (ap (μ (f *) -) f₁ ∙ right-unit-law *) ---> ap f (right-unit-law *)
                                                     α₂
  ```

  Here, the identification on the left is obtained by left whiskering the
  identification witnessing that the square

  ```text
                               ap (μ (f *)) f₁
                μ (f *) (f *) -----------------> μ (f *) *
                      |                               |
    ap (μ - (f *)) f₁ |                 β             | right-unit-law (f *)
                      ∨                               ∨
                   μ * (f *) ----------------------> f *
                               left-unit-law (f *)
  ```

  commutes, with the identification `α * * : f (μ * *) ＝ μ (f *) (f *)`. The
  quickest way to see that this square commutes is by identification elimination
  on the identification `f₁ : f * ＝ *`, using the coherence
  `left-unit-law * ＝ right-unit-law *`. Alternatively, note that all the
  squares in the diagram

  ```text
                               ap (μ (f *)) f₁
                μ (f *) (f *) -----------------> μ (f *) * --------> f *
                      |                               |               |
    ap (μ - (f *)) f₁ |                 ap (μ - *) f₁ |               |
                      ∨                               ∨               ∨
                   μ * (f *) ---------------------> μ * * ----------> *
                      |            ap (μ *) f₁        |               |
                      |                               |  coh ·r refl  | refl
                      ∨                               ∨               ∨
                     f * ---------------------------> * ------------> *
                                       f₁                  refl
  ```

  commute. Therefore we obtain an identification

  ```text
    ap (μ - (f *)) f₁ ∙ (left-unit-law (f *) ∙ f₁) ＝
    ap (μ (f *) -) f₁ ∙ (right-unit-law (f *) ∙ f₁).
  ```

  By unwhiskering of commuting squares of identifications, i.e., by canceling
  out `f₁` on both sides, it follows that the asserted square commutes.

## Definition

### The predicate of preserving left and right unit laws

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  (μ : (x y : type-Pointed-Type A) → type-Pointed-Type A)
  (ν : (x y : type-Pointed-Type B) → type-Pointed-Type B)
  (μf : preserves-mul μ ν (map-pointed-map f))
  where

  preserves-left-unit-law-mul :
    ((x : type-Pointed-Type A) → μ (point-Pointed-Type A) x ＝ x) →
    ((y : type-Pointed-Type B) → Id (ν (point-Pointed-Type B) y) y) →
    UU (l1 ⊔ l2)
  preserves-left-unit-law-mul lA lB =
    (x : type-Pointed-Type A) →
    coherence-triangle-identifications
      ( ap (map-pointed-map f) (lA x))
      ( ( ap
          ( λ t → ν t (map-pointed-map f x))
          ( preserves-point-pointed-map f)) ∙
        ( lB (map-pointed-map f x)))
      ( μf)

  preserves-right-unit-law-mul :
    ((x : type-Pointed-Type A) → μ x (point-Pointed-Type A) ＝ x) →
    ((y : type-Pointed-Type B) → ν y (point-Pointed-Type B) ＝ y) →
    UU (l1 ⊔ l2)
  preserves-right-unit-law-mul rA rB =
    (x : type-Pointed-Type A) →
    coherence-triangle-identifications
      ( ap (map-pointed-map f) (rA x))
      ( ( ap (ν (map-pointed-map f x)) (preserves-point-pointed-map f)) ∙
        ( rB (map-pointed-map f x)))
      ( μf)
```

### The predicate of preserving H-space structure on a pointed type

```agda
module _
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2)
  where

  preserves-mul-pointed-map-H-Space :
    (pointed-type-H-Space M →∗ pointed-type-H-Space N) → UU (l1 ⊔ l2)
  preserves-mul-pointed-map-H-Space f =
    preserves-mul (mul-H-Space M) (mul-H-Space N) (map-pointed-map f)

  preserves-left-unit-law-mul-pointed-map-H-Space :
    (f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
    preserves-mul-pointed-map-H-Space f → UU (l1 ⊔ l2)
  preserves-left-unit-law-mul-pointed-map-H-Space f μf =
    preserves-left-unit-law-mul f
      ( mul-H-Space M)
      ( mul-H-Space N)
      ( μf)
      ( left-unit-law-mul-H-Space M)
      ( left-unit-law-mul-H-Space N)

  preserves-right-unit-law-mul-pointed-map-H-Space :
    (f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
    preserves-mul-pointed-map-H-Space f → UU (l1 ⊔ l2)
  preserves-right-unit-law-mul-pointed-map-H-Space f μf =
    preserves-right-unit-law-mul f
      ( mul-H-Space M)
      ( mul-H-Space N)
      ( μf)
      ( right-unit-law-mul-H-Space M)
      ( right-unit-law-mul-H-Space N)

  coherence-square-unit-laws-preserves-point-pointed-map-H-Space :
    (f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
    coherence-square-identifications
      ( ap
        ( mul-H-Space N (map-pointed-map f (unit-H-Space M)))
        ( preserves-point-pointed-map f))
      ( ap
        ( mul-H-Space' N (map-pointed-map f (unit-H-Space M)))
        ( preserves-point-pointed-map f))
      ( right-unit-law-mul-H-Space N (map-pointed-map f (unit-H-Space M)))
      ( left-unit-law-mul-H-Space N (map-pointed-map f (unit-H-Space M)))
  coherence-square-unit-laws-preserves-point-pointed-map-H-Space (f , refl) =
    coh-unit-laws-mul-H-Space N

  preserves-coherence-unit-laws-mul-pointed-map-H-Space :
    (f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
    (μ : preserves-mul-pointed-map-H-Space f) →
    (ν : preserves-left-unit-law-mul-pointed-map-H-Space f μ) →
    (ρ : preserves-right-unit-law-mul-pointed-map-H-Space f μ) → UU l2
  preserves-coherence-unit-laws-mul-pointed-map-H-Space f μ ν ρ =
    coherence-square-identifications
      ( ν (unit-H-Space M))
      ( ap² (map-pointed-map f) (coh-unit-laws-mul-H-Space M))
      ( left-whisker-concat
        ( μ)
        ( coherence-square-unit-laws-preserves-point-pointed-map-H-Space f))
      ( ρ (unit-H-Space M))

  preserves-unital-mul-pointed-map-H-Space :
    (f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
    UU (l1 ⊔ l2)
  preserves-unital-mul-pointed-map-H-Space f =
    Σ ( preserves-mul-pointed-map-H-Space f)
      ( λ μ →
        Σ ( preserves-left-unit-law-mul-pointed-map-H-Space f μ)
          ( λ ν →
            Σ ( preserves-right-unit-law-mul-pointed-map-H-Space f μ)
              ( preserves-coherence-unit-laws-mul-pointed-map-H-Space f μ ν)))
```

### Morphisms of H-spaces

```agda
module _
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2)
  where

  hom-H-Space : UU (l1 ⊔ l2)
  hom-H-Space =
    Σ ( pointed-type-H-Space M →∗ pointed-type-H-Space N)
      ( preserves-unital-mul-pointed-map-H-Space M N)

module _
  {l1 l2 : Level} {M : H-Space l1} {N : H-Space l2} (f : hom-H-Space M N)
  where

  pointed-map-hom-H-Space : pointed-type-H-Space M →∗ pointed-type-H-Space N
  pointed-map-hom-H-Space = pr1 f

  map-hom-H-Space : type-H-Space M → type-H-Space N
  map-hom-H-Space = map-pointed-map pointed-map-hom-H-Space

  preserves-unit-hom-H-Space :
    map-hom-H-Space (unit-H-Space M) ＝ unit-H-Space N
  preserves-unit-hom-H-Space =
    preserves-point-pointed-map pointed-map-hom-H-Space

  preserves-unital-mul-hom-H-Space :
    preserves-unital-mul-pointed-map-H-Space M N pointed-map-hom-H-Space
  preserves-unital-mul-hom-H-Space = pr2 f

  preserves-mul-hom-H-Space :
    preserves-mul-pointed-map-H-Space M N pointed-map-hom-H-Space
  preserves-mul-hom-H-Space =
    pr1 preserves-unital-mul-hom-H-Space

  preserves-left-unit-law-mul-hom-H-Space :
    preserves-left-unit-law-mul-pointed-map-H-Space M N
      ( pointed-map-hom-H-Space)
      ( preserves-mul-hom-H-Space)
  preserves-left-unit-law-mul-hom-H-Space =
    pr1 (pr2 preserves-unital-mul-hom-H-Space)

  preserves-right-unit-law-mul-hom-H-Space :
    preserves-right-unit-law-mul-pointed-map-H-Space M N
      ( pointed-map-hom-H-Space)
      ( preserves-mul-hom-H-Space)
  preserves-right-unit-law-mul-hom-H-Space =
    pr1 (pr2 (pr2 preserves-unital-mul-hom-H-Space))

  preserves-coherence-unit-laws-mul-hom-H-Space :
    preserves-coherence-unit-laws-mul-pointed-map-H-Space M N
      ( pointed-map-hom-H-Space)
      ( preserves-mul-hom-H-Space)
      ( preserves-left-unit-law-mul-hom-H-Space)
      ( preserves-right-unit-law-mul-hom-H-Space)
  preserves-coherence-unit-laws-mul-hom-H-Space =
    pr2 (pr2 (pr2 preserves-unital-mul-hom-H-Space))
```

### Homotopies of morphisms of H-spaces

```agda
preserves-mul-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (μA : A → A → A) (μB : B → B → B) →
  {f g : A → B} (μf : preserves-mul μA μB f) (μg : preserves-mul μA μB g) →
  (f ~ g) → UU (l1 ⊔ l2)
preserves-mul-htpy {A = A} μA μB μf μg H =
  (a b : A) → Id (μf ∙ ap-binary μB (H a) (H b)) (H (μA a b) ∙ μg)
```
