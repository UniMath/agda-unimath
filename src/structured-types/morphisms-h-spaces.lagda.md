# Morphisms of H-spaces

```agda
module structured-types.morphisms-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
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
{{#concept "morphism of H-spaces"}} from `X` to `Y` consists of a
[pointed map](structured-types.pointed-maps.md) `f : X →∗ Y` that preserves the
unital binary operation

```text
  α : (x x' : X) → f (μ x x') ＝ μ (f x) (f x')
```

and which furthermore comes equipped with the following structure, witnessing
that the unit laws are preserved:

- For each `x' : X` an identification `α₁ x'` witnessing that the diagram

  ```text
                         f (μ * x')
                            |   \
                            |    \ α * x'
                            |     ∨
                            |  μ (f *) (f x')
                            |      |
    ap f (left-unit-law x') |      | ap (μ - (f x')) f₁
                            |      ∨
                            |    μ * (f x')
                            |     /
                            |    / left-unit-law (f x')
                            ∨   ∨
                            f x'
  ```

  commutes.

- For each `x : X` an identification `α₂ x` witnessing that the diagram

  ```text
                         f (μ x *)
                           /    |
                    α x * /     |
                         ∨      |
                μ (f x) (f *)   |
                        |       |
      ap (μ (f x) -) f₁ |       | ap f (right-unit-law x)
                        ∨       |
                  μ * (f x)     |
                         \      |
     right-unit-law (f x) \     |
                           ∨    ∨
                             f x
  ```

  commutes.

- An identification `α₃` witnessing that the square

  ```text
                                                    α₁ _
     α₀ * * ∙ (ap (μ - (f *)) f₁ ∙ left-unit-law *) ---> ap f (left-unit-law *)
                       |                                         |
         (α₀ * *) ·l β |                                         |
                       ∨                                         ∨
    α₀ * * ∙ (ap (μ (f *) -) f₁ ∙ right-unit-law *) ---> ap f (right-unit-law *)
                                                    α₂ _
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
                μ (f *) (f *) -----------------> μ (f *) * ------> f *
                      |                               |             |
    ap (μ - (f *)) f₁ |                 ap (μ - *) f₁ |             |
                      ∨                               ∨             ∨
                   μ * (f *) ---------------------> μ * * --------> *
                      |            ap (μ *) f₁        |             |
                      |                               | coh ·r refl | refl
                      ∨                               ∨             ∨
                     f * ---------------------------> * ----------> *
                                       f₁                  refl
  ```

  commute. Therefore we obtain an identification

  ```text
    ap (μ - (f *)) f₁ ∙ (left-unit-law (f *) ∙ f₁) ＝
    ap (μ (f *) -) f₁ ∙ (right-unit-law (f *) ∙ f₁).
  ```

  By unwhiskering of commuting squares of identifications, i.e., by cancelling
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

### The predicate of preserving the coherence between unit laws

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

  preserves-coherence-unit-laws-mul-pointed-map-H-Space :
    (f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
    (μ : preserves-mul-pointed-map-H-Space f) →
    (ν : preserves-left-unit-law-mul-pointed-map-H-Space f μ) →
    (ρ : preserves-right-unit-law-mul-pointed-map-H-Space f μ) → UU {!!}
  preserves-coherence-unit-laws-mul-pointed-map-H-Space (f , refl) μ ν ρ =
    {!coherence-square-identifications!}
```

### The predicate of preserving H-space structure on a pointed type

```agda
module _
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2)
  (f : pointed-type-H-Space M →∗ pointed-type-H-Space N)
  where

preserves-coh-unit-laws-mul :
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2) →
  ( f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
  ( μf :
    preserves-mul (mul-H-Space M) (mul-H-Space N) (pr1 f)) →
  preserves-left-unit-law-mul f
    ( mul-H-Space M)
    ( mul-H-Space N)
    ( μf)
    ( left-unit-law-mul-H-Space M)
    ( left-unit-law-mul-H-Space N) →
  preserves-right-unit-law-mul f
    ( mul-H-Space M)
    ( mul-H-Space N)
    ( μf)
    ( right-unit-law-mul-H-Space M)
    ( right-unit-law-mul-H-Space N) →
  UU l2
preserves-coh-unit-laws-mul M
  (pair (pair N ._) μ)
  (pair f refl) μf lf rf =
  Id (ap² f cM ∙ rf eM) (lf eM ∙ ap (concat μf (f eM)) cN)
  where
  eM = unit-H-Space M
  cM = coh-unit-laws-mul-H-Space M
  cN = pr2 (pr2 (pr2 μ))
```

### Second description of preservation of the coherent unit laws

```agda
preserves-coh-unit-laws-mul' :
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2) →
  ( f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
  ( μf :
    preserves-mul (mul-H-Space M) (mul-H-Space N) (pr1 f)) →
  preserves-left-unit-law-mul f
    ( mul-H-Space M)
    ( mul-H-Space N)
    ( μf)
    ( left-unit-law-mul-H-Space M)
    ( left-unit-law-mul-H-Space N) →
  preserves-right-unit-law-mul f
    ( mul-H-Space M)
    ( mul-H-Space N)
    ( μf)
    ( right-unit-law-mul-H-Space M)
    ( right-unit-law-mul-H-Space N) →
  UU l2
preserves-coh-unit-laws-mul' M N f μf lf rf =
  Id
    { A =
      Id (ap (pr1 f) (lM eM) ∙ ef) ((μf ∙ ap-binary μN ef ef) ∙ rN eN)}
    ( ( horizontal-concat-Id² (lf eM) (inv (ap-id ef))) ∙
      ( ( right-whisker-concat
          ( inv
            ( assoc
              ( μf)
              ( ap (mul-H-Space' N (pr1 f eM)) ef)
              ( lN (pr1 f eM))))
          ( ap id ef)) ∙
        ( ( assoc
            ( μf ∙ ap (mul-H-Space' N (pr1 f eM)) ef)
            ( lN (pr1 f eM))
            ( ap id ef)) ∙
          ( ( left-whisker-concat
              ( μf ∙ ap (mul-H-Space' N (pr1 f eM)) ef)
              ( nat-htpy lN ef)) ∙
            ( ( inv
                ( assoc
                  ( μf ∙ ap (mul-H-Space' N (pr1 f eM)) ef)
                  ( ap (μN eN) ef)
                  ( lN eN))) ∙
              ( ( ap
                  ( λ t → t ∙ lN eN)
                  ( assoc
                    ( μf)
                    ( ap (mul-H-Space' N (pr1 f eM)) ef)
                    ( ap (μN eN) ef))) ∙
                ( horizontal-concat-Id²
                  ( left-whisker-concat
                    ( μf)
                    ( inv (triangle-ap-binary μN ef ef)))
                  ( cN))))))))
    ( ( right-whisker-concat (ap² (pr1 f) cM) ef) ∙
      ( ( horizontal-concat-Id² (rf eM) (inv (ap-id ef))) ∙
        ( ( right-whisker-concat
            ( inv
              ( assoc
                ( μf) (ap (μN (pr1 f eM)) ef) (rN (pr1 f eM))))
            ( ap id ef)) ∙
          ( ( assoc
              ( μf ∙ ap (μN (pr1 f eM)) ef)
              ( rN (pr1 f eM))
              ( ap id ef)) ∙
            ( ( left-whisker-concat
                ( μf ∙ ap (μN (pr1 f eM)) ef)
                ( nat-htpy rN ef)) ∙
              ( ( inv
                  ( assoc
                    ( μf ∙ ap (μN (pr1 f eM)) ef)
                    ( ap (mul-H-Space' N eN) ef)
                    ( rN eN))) ∙
                ( ap
                  ( λ t → t ∙ rN eN)
                  ( ( assoc
                      ( μf)
                      ( ap (μN (pr1 f eM)) ef)
                      ( ap (mul-H-Space' N eN) ef)) ∙
                    ( left-whisker-concat
                      ( μf)
                      ( inv (triangle-ap-binary' μN ef ef)))))))))))
  where
  eM = unit-H-Space M
  μM = mul-H-Space M
  lM = left-unit-law-mul-H-Space M
  rM = right-unit-law-mul-H-Space M
  cM = coh-unit-laws-mul-H-Space M
  eN = unit-H-Space N
  μN = mul-H-Space N
  lN = left-unit-law-mul-H-Space N
  rN = right-unit-law-mul-H-Space N
  cN = coh-unit-laws-mul-H-Space N
  ef = pr2 f

preserves-unital-mul :
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2) →
  (f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
  UU (l1 ⊔ l2)
preserves-unital-mul M N f =
  Σ ( preserves-mul μM μN (pr1 f))
    ( λ μ11 →
      Σ ( preserves-left-unit-law-mul f μM μN μ11 lM lN)
        ( λ μ01 →
          Σ ( preserves-right-unit-law-mul f μM μN μ11 rM rN)
            ( λ μ10 → preserves-coh-unit-laws-mul M N f μ11 μ01 μ10)))
  where
  μM = mul-H-Space M
  lM = left-unit-law-mul-H-Space M
  rM = right-unit-law-mul-H-Space M
  μN = mul-H-Space N
  lN = left-unit-law-mul-H-Space N
  rN = right-unit-law-mul-H-Space N

hom-H-Space :
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2) →
  UU (l1 ⊔ l2)
hom-H-Space M N =
  Σ ( pointed-type-H-Space M →∗ pointed-type-H-Space N)
    ( preserves-unital-mul M N)
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
