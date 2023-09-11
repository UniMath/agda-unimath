# Sections of families over the circle

```agda
module synthetic-homotopy-theory.sections-descent-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

Sections of type families over the [circle](synthetic-homotopy-theory.circle.md)
are exactly the fixpoints of the [automorphism](foundation.automorphisms.md)
from the corresponding
[descent data](synthetic-homotopy-theory.descent-circle.md).

## Definitions

### Fixpoints of descent data

A fixpoint of `(X, e)` is a fixpoint of `e`.

```agda
fixpoint-descent-data-circle :
  { l1 : Level}
  ( P : descent-data-circle l1) → UU l1
fixpoint-descent-data-circle P =
  Σ ( type-descent-data-circle P)
    ( λ x → (map-descent-data-circle P x) ＝ x)
```

## Properties

### Characterization of sections of type families over the circle

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  where

  map-compute-dependent-identification-loop-circle :
    ( x y : type-family-with-descent-data-circle A) →
    map-aut-family-with-descent-data-circle A x ＝ y →
    dependent-identification (family-family-with-descent-data-circle A)
      ( loop-free-loop l)
      ( map-equiv-family-with-descent-data-circle A x)
      ( map-equiv-family-with-descent-data-circle A y)
  map-compute-dependent-identification-loop-circle x y q =
    inv (coherence-square-family-with-descent-data-circle A x) ∙
    ( ap (map-equiv-family-with-descent-data-circle A) q)

  is-equiv-map-compute-dependent-identification-loop-circle :
    ( x y : type-family-with-descent-data-circle A) →
    is-equiv (map-compute-dependent-identification-loop-circle x y)
  is-equiv-map-compute-dependent-identification-loop-circle x y =
    fundamental-theorem-id
      ( is-contr-equiv'
        ( fiber
          ( map-equiv-family-with-descent-data-circle A)
          ( tr
            ( family-family-with-descent-data-circle A)
            ( loop-free-loop l)
            ( map-equiv-family-with-descent-data-circle A x)))
        ( equiv-fiber _ _)
        ( is-contr-map-is-equiv
          ( is-equiv-map-equiv (equiv-family-with-descent-data-circle A))
          ( tr
            ( family-family-with-descent-data-circle A)
            ( loop-free-loop l)
            ( map-equiv-family-with-descent-data-circle A x))))
      ( map-compute-dependent-identification-loop-circle x)
      ( y)

  compute-dependent-identification-loop-circle :
    ( x y : type-family-with-descent-data-circle A) →
    ( map-aut-family-with-descent-data-circle A x ＝ y) ≃
    ( dependent-identification
      ( family-family-with-descent-data-circle A)
      ( loop-free-loop l)
      ( map-equiv-family-with-descent-data-circle A x)
      ( map-equiv-family-with-descent-data-circle A y))
  pr1 (compute-dependent-identification-loop-circle x y) =
    map-compute-dependent-identification-loop-circle x y
  pr2 (compute-dependent-identification-loop-circle x y) =
    is-equiv-map-compute-dependent-identification-loop-circle x y
```

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  where

  ev-fixpoint-descent-data-circle :
    ( (x : S) → family-family-with-descent-data-circle A x) →
    ( fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle A))
  pr1 (ev-fixpoint-descent-data-circle s) =
    map-inv-equiv
      ( equiv-family-with-descent-data-circle A)
      ( s (base-free-loop l))
  pr2 (ev-fixpoint-descent-data-circle s) =
    map-inv-equiv
      ( compute-dependent-identification-loop-circle
        ( l)
        ( A)
        ( map-inv-equiv
          ( equiv-family-with-descent-data-circle A)
          ( s (base-free-loop l)))
        ( map-inv-equiv
          ( equiv-family-with-descent-data-circle A)
          ( s (base-free-loop l))))
      ( ( ap
          ( tr (family-family-with-descent-data-circle A) (loop-free-loop l))
          ( is-section-map-inv-equiv
            ( equiv-family-with-descent-data-circle A)
            ( s (base-free-loop l)))) ∙
        ( ( apd s (loop-free-loop l)) ∙
          ( inv
            ( is-section-map-inv-equiv
              ( equiv-family-with-descent-data-circle A)
              ( s (base-free-loop l))))))

  equiv-fixpoint-descent-data-circle-free-dependent-loop :
    ( fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)) ≃
    ( free-dependent-loop l (family-family-with-descent-data-circle A))
  equiv-fixpoint-descent-data-circle-free-dependent-loop =
    equiv-Σ
      ( λ x →
        dependent-identification
          ( family-family-with-descent-data-circle A)
          ( loop-free-loop l)
          ( x)
          ( x))
      ( equiv-family-with-descent-data-circle A)
      ( λ x →
        compute-dependent-identification-loop-circle l A x x)

  comparison-fixpoint-descent-data-circle :
    ( fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)) →
    ( free-dependent-loop l (family-family-with-descent-data-circle A))
  comparison-fixpoint-descent-data-circle =
    map-equiv equiv-fixpoint-descent-data-circle-free-dependent-loop

  triangle-comparison-fixpoint-descent-data-circle :
    coherence-triangle-maps
      ( ev-free-loop-Π l (family-family-with-descent-data-circle A))
      ( comparison-fixpoint-descent-data-circle)
      ( ev-fixpoint-descent-data-circle)
  triangle-comparison-fixpoint-descent-data-circle s =
    eq-Eq-free-dependent-loop l
      ( family-family-with-descent-data-circle A)
      ( ev-free-loop-Π l (family-family-with-descent-data-circle A) s)
      ( ( comparison-fixpoint-descent-data-circle ∘
          ev-fixpoint-descent-data-circle)
        ( s))
      ( inv is-section-inv-α ,
        inv
        ( ( horizontal-concat-Id²
            ( refl
              { x =
                ap
                  ( tr
                    ( family-family-with-descent-data-circle A)
                    ( loop-free-loop l))
                  ( inv is-section-inv-α)})
            ( is-section-map-inv-is-equiv
              ( is-equiv-map-compute-dependent-identification-loop-circle
                ( l)
                ( A)
                ( map-inv-equiv
                  ( equiv-family-with-descent-data-circle A)
                  ( s (base-free-loop l)))
                ( pr1 (ev-fixpoint-descent-data-circle s)))
              ( _))) ∙
          ( ( inv (assoc (ap _ (inv is-section-inv-α)) _ _)) ∙
            ( horizontal-concat-Id²
              ( inv
                ( ap-concat-eq
                  ( tr
                    ( family-family-with-descent-data-circle A)
                    ( loop-free-loop l))
                  ( inv is-section-inv-α)
                  ( is-section-inv-α)
                  ( refl)
                  ( inv (left-inv is-section-inv-α))))
              ( refl)))))
    where
    is-section-inv-α :
      eq-value
        ( map-equiv-family-with-descent-data-circle A ∘
          map-inv-equiv (equiv-family-with-descent-data-circle A))
        ( id)
        ( s (base-free-loop l))
    is-section-inv-α =
      is-section-map-inv-equiv
        ( equiv-family-with-descent-data-circle A)
        ( s (base-free-loop l))

  is-equiv-comparison-fixpoint-descent-data-circle :
    is-equiv comparison-fixpoint-descent-data-circle
  is-equiv-comparison-fixpoint-descent-data-circle =
    is-equiv-map-equiv equiv-fixpoint-descent-data-circle-free-dependent-loop

  is-equiv-ev-fixpoint-descent-data-circle :
    ( dependent-universal-property-circle l2 l) →
    is-equiv ev-fixpoint-descent-data-circle
  is-equiv-ev-fixpoint-descent-data-circle dup-circle =
    is-equiv-right-factor-htpy
      ( ev-free-loop-Π l (family-family-with-descent-data-circle A))
      ( comparison-fixpoint-descent-data-circle)
      ( ev-fixpoint-descent-data-circle)
      ( triangle-comparison-fixpoint-descent-data-circle)
      ( is-equiv-comparison-fixpoint-descent-data-circle)
      ( dup-circle (family-family-with-descent-data-circle A))

  equiv-ev-fixpoint-descent-data-circle :
    ( dependent-universal-property-circle l2 l) →
    ( (x : S) → (family-family-with-descent-data-circle A) x) ≃
    ( fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle A))
  pr1 (equiv-ev-fixpoint-descent-data-circle dup-circle) =
    ev-fixpoint-descent-data-circle
  pr2 (equiv-ev-fixpoint-descent-data-circle dup-circle) =
    is-equiv-ev-fixpoint-descent-data-circle dup-circle

  compute-ev-fixpoint-descent-data-circle :
    coherence-square-maps
      ( ev-fixpoint-descent-data-circle)
      ( ev-point (base-free-loop l))
      ( pr1)
      ( map-inv-equiv (equiv-family-with-descent-data-circle A))
  compute-ev-fixpoint-descent-data-circle = refl-htpy
```
