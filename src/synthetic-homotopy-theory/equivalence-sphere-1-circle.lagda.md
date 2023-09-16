# Equivalence between the first sphere and the circle

```agda
module synthetic-homotopy-theory.equivalence-sphere-1-circle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.retractions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The first sphere is defined as having two points `N` and `S` and two
identifications (meridians) `e, w : N = S` between them. The map from the circle
to the first sphere is defined by mapping the basepoint to `N` and the loop to
the composite of `e` and the inverse of `w`, while the map from the first sphere
to the circle is defined by mapping both `N` and `S` to the basepoint, `e` to
the loop and `w` to `refl` at the basepoint. Some care needs to be taken when
proving these are inverse, as `S` is first mapped to the basepoint and then back
to `N`. It needs to be further identified with `S` using one of the meridians
and the correct choice turns out to be `w`.

### The map from the first sphere to the circle

```agda
map-sphere-0-eq-base-𝕊¹ : (sphere 0) → base-𝕊¹ ＝ base-𝕊¹
map-sphere-0-eq-base-𝕊¹ (inl n) = loop-𝕊¹
map-sphere-0-eq-base-𝕊¹ (inr n) = refl

suspension-structure-sphere-0-𝕊¹ :
  suspension-structure (sphere 0) 𝕊¹
suspension-structure-sphere-0-𝕊¹ =
  (base-𝕊¹ , base-𝕊¹ , map-sphere-0-eq-base-𝕊¹)

circle-sphere-1 : sphere 1 → 𝕊¹
circle-sphere-1 =
  map-inv-up-suspension
    ( sphere 0)
    ( 𝕊¹)
    ( suspension-structure-sphere-0-𝕊¹)

circle-sphere-1-north-sphere-1-eq-base-𝕊¹ :
  Id (circle-sphere-1 (north-sphere 1)) base-𝕊¹
circle-sphere-1-north-sphere-1-eq-base-𝕊¹ =
  up-suspension-north-suspension
    (sphere 0)
    ( 𝕊¹)
    ( suspension-structure-sphere-0-𝕊¹)

circle-sphere-1-south-sphere-1-eq-base-𝕊¹ :
  Id (circle-sphere-1 (south-sphere 1)) base-𝕊¹
circle-sphere-1-south-sphere-1-eq-base-𝕊¹ =
  up-suspension-south-suspension
    ( sphere 0)
    ( 𝕊¹)
    ( suspension-structure-sphere-0-𝕊¹)
```

### The map from the circle to the first sphere

```agda
north-sphere-1-loop : Id (north-sphere 1) (north-sphere 1)
north-sphere-1-loop =
  ( meridian-sphere 0 (zero-Fin 1)) ∙
  ( inv (meridian-sphere 0 (one-Fin 1)))

sphere-1-circle : 𝕊¹ → sphere 1
sphere-1-circle =
  map-apply-universal-property-𝕊¹ (north-sphere 1) north-sphere-1-loop

sphere-1-circle-base-𝕊¹-eq-north-sphere-1 :
  Id (sphere-1-circle base-𝕊¹) (north-sphere 1)
sphere-1-circle-base-𝕊¹-eq-north-sphere-1 =
  base-universal-property-𝕊¹ (north-sphere 1) north-sphere-1-loop

sphere-1-circle-base-𝕊¹-eq-south-sphere-1 :
  Id (sphere-1-circle base-𝕊¹) (south-sphere 1)
sphere-1-circle-base-𝕊¹-eq-south-sphere-1 =
  ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1) ∙
  ( meridian-sphere 0 (one-Fin 1))
```

### The map from the first first sphere to the circle has a section

```agda
circle-sphere-1-circle-base-𝕊¹ :
  Id (circle-sphere-1 (sphere-1-circle base-𝕊¹)) base-𝕊¹
circle-sphere-1-circle-base-𝕊¹ =
  ( ap circle-sphere-1 sphere-1-circle-base-𝕊¹-eq-north-sphere-1) ∙
  ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)

apply-up-suspension-meridian-one-suspension-circle-sphere-1-circle :
  coherence-square-identifications
    ( ap circle-sphere-1 (inv (meridian-sphere 0 (one-Fin 1))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
    ( refl)
    ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹)
apply-up-suspension-meridian-one-suspension-circle-sphere-1-circle =
  ( identification-right-whisk
    ( ap-inv
      ( circle-sphere-1)
      ( meridian-suspension (one-Fin 1)))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
  ( inv right-unit) ∙
  ( assoc
    ( inv (ap circle-sphere-1 (meridian-suspension (one-Fin 1))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
    ( refl)) ∙
  ( identification-left-whisk
    ( inv (ap circle-sphere-1 (meridian-suspension (one-Fin 1))))
    ( inv
      ( up-suspension-meridian-suspension
        (sphere 0) 𝕊¹ suspension-structure-sphere-0-𝕊¹ (one-Fin 1)))) ∙
  ( inv
    ( assoc
      ( inv (ap circle-sphere-1 (meridian-suspension (one-Fin 1))))
      ( ap circle-sphere-1 (meridian-suspension (one-Fin 1)))
      ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹))) ∙
  ( identification-right-whisk
    ( left-inv (ap circle-sphere-1 (meridian-suspension (one-Fin 1))))
    ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹))

apply-up-suspension-meridian-zero-suspension-circle-sphere-1-circle :
  coherence-square-identifications
    ( ap (circle-sphere-1) (north-sphere-1-loop))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
    ( loop-𝕊¹)
apply-up-suspension-meridian-zero-suspension-circle-sphere-1-circle =
  ( identification-right-whisk
    ( ap-concat
      ( circle-sphere-1)
      ( meridian-sphere 0 (zero-Fin 1))
      ( inv (meridian-suspension (one-Fin 1))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
  ( assoc
    ( ap circle-sphere-1 (meridian-suspension (zero-Fin 1)))
    ( ap circle-sphere-1 (inv ( meridian-sphere 0 (one-Fin 1))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
  ( identification-left-whisk
    ( ap circle-sphere-1 (meridian-suspension (zero-Fin 1)))
    ( apply-up-suspension-meridian-one-suspension-circle-sphere-1-circle)) ∙
  ( up-suspension-meridian-suspension
    ( sphere 0)
    ( 𝕊¹)
    ( suspension-structure-sphere-0-𝕊¹ (zero-Fin 1)))

circle-sphere-1-circle-loop-𝕊¹ :
  coherence-square-identifications
    ( ap circle-sphere-1 (ap sphere-1-circle loop-𝕊¹))
    ( circle-sphere-1-circle-base-𝕊¹)
    ( circle-sphere-1-circle-base-𝕊¹)
    ( loop-𝕊¹)
circle-sphere-1-circle-loop-𝕊¹ =
  inv
    ( assoc
      ( ap circle-sphere-1 (ap sphere-1-circle loop-𝕊¹))
      ( ap
        ( circle-sphere-1)
        ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
    ( identification-right-whisk
      ( inv
        ( ap-concat
          ( circle-sphere-1)
          ( ap sphere-1-circle loop-𝕊¹)
          ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹) ∙
    ( identification-right-whisk
      ( ap
        ( ap circle-sphere-1)
        ( loop-universal-property-𝕊¹
          ( north-sphere 1)
          ( north-sphere-1-loop)))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹) ∙
    ( identification-right-whisk
      ( ap-concat
        ( circle-sphere-1)
        ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
        ( north-sphere-1-loop))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹) ∙
    ( assoc
      ( ap circle-sphere-1 sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
      ( ap circle-sphere-1 north-sphere-1-loop)
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹) ∙
    ( identification-left-whisk
      ( ap circle-sphere-1 sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
      ( apply-up-suspension-meridian-zero-suspension-circle-sphere-1-circle) ∙
    ( inv
      ( assoc
        ( ap circle-sphere-1 sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
        ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
        ( loop-𝕊¹))))))))

circle-sphere-1-circle : section circle-sphere-1
pr1 circle-sphere-1-circle = sphere-1-circle
pr2 circle-sphere-1-circle =
  function-apply-dependent-universal-property-𝕊¹
    ( λ x → Id (circle-sphere-1 (sphere-1-circle x)) x)
    ( circle-sphere-1-circle-base-𝕊¹)
    ( map-compute-dependent-identification-eq-value-comp-id
      ( circle-sphere-1)
      ( sphere-1-circle)
      ( loop-𝕊¹)
      ( circle-sphere-1-circle-base-𝕊¹)
      ( circle-sphere-1-circle-base-𝕊¹)
      ( circle-sphere-1-circle-loop-𝕊¹))
```

### The map from the first first sphere to the circle has a retraction

```agda
sphere-1-circle-sphere-1-north-sphere-1 :
  Id
    ( sphere-1-circle (circle-sphere-1 (north-sphere 1)))
    ( north-sphere 1)
sphere-1-circle-sphere-1-north-sphere-1 =
  ( ap sphere-1-circle circle-sphere-1-north-sphere-1-eq-base-𝕊¹) ∙
  ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)

sphere-1-circle-sphere-1-south-sphere-1 :
  Id
    ( sphere-1-circle (circle-sphere-1 (south-sphere 1)))
    ( south-sphere 1)
sphere-1-circle-sphere-1-south-sphere-1 =
  ( ap sphere-1-circle circle-sphere-1-south-sphere-1-eq-base-𝕊¹) ∙
  ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)

apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1 :
  ( n : Fin 2) →
    ( coherence-square-identifications
      ( ap sphere-1-circle (ap circle-sphere-1 (meridian-suspension n)))
      ( sphere-1-circle-sphere-1-south-sphere-1)
      ( ap
        ( sphere-1-circle)
        ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹ ∙
          map-sphere-0-eq-base-𝕊¹ n))
      ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1))
apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1 n =
  ( inv
    ( assoc
      ( ap sphere-1-circle (ap circle-sphere-1 (meridian-suspension n)))
      ( ap sphere-1-circle circle-sphere-1-south-sphere-1-eq-base-𝕊¹)
      ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)) ∙
  ( identification-right-whisk
    ( inv
      ( ap-concat
        ( sphere-1-circle)
        ( ap circle-sphere-1 (meridian-sphere 0 n))
        ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹)))
    ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)) ∙
  ( ap
    ( λ x →
      ( ap sphere-1-circle x) ∙
      ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1))
    ( up-suspension-meridian-suspension
      (sphere 0) 𝕊¹ suspension-structure-sphere-0-𝕊¹ n)))

apply-loop-universal-property-𝕊¹-sphere-1-circle-sphere-1 :
  coherence-square-identifications
    ( ap sphere-1-circle loop-𝕊¹)
    ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)
    ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
    ( meridian-sphere 0 (zero-Fin 1))
apply-loop-universal-property-𝕊¹-sphere-1-circle-sphere-1 =
  ( inv
    ( assoc
      ( ap sphere-1-circle loop-𝕊¹)
      ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
      ( meridian-sphere 0 (one-Fin 1))) ∙
  ( identification-right-whisk
    ( loop-universal-property-𝕊¹
      ( north-sphere 1)
      ( north-sphere-1-loop))
    ( meridian-sphere 0 (one-Fin 1)) ∙
  ( assoc
    ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
    ( north-sphere-1-loop)
    ( meridian-sphere 0 (one-Fin 1)) ∙
  ( identification-left-whisk
    ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
    ( is-section-right-concat-inv
      ( meridian-sphere 0 (zero-Fin 1))
      ( meridian-sphere 0 (one-Fin 1)))))))

map-sphere-1-circle-sphere-1-meridian :
  ( n : Fin 2) →
  ( dependent-identification
    ( λ x → Id (sphere-1-circle (circle-sphere-1 x)) x)
    ( meridian-suspension-structure
      ( suspension-structure-suspension (Fin 2)) n)
    ( sphere-1-circle-sphere-1-north-sphere-1)
    ( sphere-1-circle-sphere-1-south-sphere-1))
map-sphere-1-circle-sphere-1-meridian (inl (inr n)) =
  map-compute-dependent-identification-eq-value-comp-id
    ( sphere-1-circle)
    ( circle-sphere-1)
    ( meridian-sphere 0 (inl (inr n)))
    ( sphere-1-circle-sphere-1-north-sphere-1)
    ( sphere-1-circle-sphere-1-south-sphere-1)
    ( apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1
      (inl (inr n)) ∙
    ( identification-right-whisk
      ( ap-concat
        ( sphere-1-circle)
        ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
        ( loop-𝕊¹))
      ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1) ∙
    ( assoc
      ( ap sphere-1-circle (circle-sphere-1-north-sphere-1-eq-base-𝕊¹))
      ( ap sphere-1-circle loop-𝕊¹)
      ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1) ∙
    ( identification-left-whisk
      ( ap sphere-1-circle (circle-sphere-1-north-sphere-1-eq-base-𝕊¹))
      ( apply-loop-universal-property-𝕊¹-sphere-1-circle-sphere-1) ∙
    ( inv
      ( assoc
        ( ap sphere-1-circle (circle-sphere-1-north-sphere-1-eq-base-𝕊¹))
        ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
        ( meridian-sphere 0 (zero-Fin 1))))))))
map-sphere-1-circle-sphere-1-meridian (inr n) =
  map-compute-dependent-identification-eq-value-comp-id
    ( sphere-1-circle)
    ( circle-sphere-1)
    ( meridian-sphere 0 (inr n))
    ( sphere-1-circle-sphere-1-north-sphere-1)
    ( sphere-1-circle-sphere-1-south-sphere-1)
    ( apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1
      ( inr n) ∙
    ( ap
      ( λ x →
        ( ap sphere-1-circle x) ∙
        ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1))
      ( right-unit {p = circle-sphere-1-north-sphere-1-eq-base-𝕊¹}) ∙
    ( inv
      ( assoc
        ( ap sphere-1-circle circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
          ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
          ( meridian-sphere 0 (one-Fin 1))))))

dependent-suspension-structure-sphere-1-circle-sphere-1 :
  dependent-suspension-structure
    ( λ x → Id (sphere-1-circle (circle-sphere-1 x)) x)
    ( suspension-structure-suspension (Fin 2))
dependent-suspension-structure-sphere-1-circle-sphere-1 =
  ( sphere-1-circle-sphere-1-north-sphere-1 ,
    sphere-1-circle-sphere-1-south-sphere-1 ,
    map-sphere-1-circle-sphere-1-meridian)

sphere-1-circle-sphere-1 : retraction circle-sphere-1
pr1 sphere-1-circle-sphere-1 = sphere-1-circle
pr2 sphere-1-circle-sphere-1 =
  map-inv-dependent-up-suspension
    ( λ x → Id (sphere-1-circle (circle-sphere-1 x)) x)
    ( dependent-suspension-structure-sphere-1-circle-sphere-1)
```

### The equivalence between the first sphere and the circle

```agda
is-equiv-circle-sphere-1 : is-equiv circle-sphere-1
is-equiv-circle-sphere-1 =
  ( circle-sphere-1-circle , sphere-1-circle-sphere-1)

equiv-circle-sphere-1 : sphere 1 ≃ 𝕊¹
pr1 equiv-circle-sphere-1 = circle-sphere-1
pr2 equiv-circle-sphere-1 = is-equiv-circle-sphere-1
```
