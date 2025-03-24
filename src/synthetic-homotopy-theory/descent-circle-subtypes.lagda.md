# Subtypes of descent data for the circle

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.descent-circle-subtypes
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-descent-circle funext univalence truncations
open import synthetic-homotopy-theory.descent-circle funext univalence truncations
open import synthetic-homotopy-theory.descent-circle-dependent-pair-types funext univalence truncations
open import synthetic-homotopy-theory.free-loops funext univalence truncations
open import synthetic-homotopy-theory.sections-descent-circle funext univalence truncations
open import synthetic-homotopy-theory.universal-property-circle funext univalence truncations
```

</details>

## Idea

Given a family `A : 𝕊¹ → U` over the
[circle](synthetic-homotopy-theory.circle.md) and a family
`B : (t : 𝕊¹) → (A t) → U` over `A` with corresponding
[descent data](synthetic-homotopy-theory.descent-circle.md) `(X, e)` and
dependent descent data `(R, k)`, where `R` is a
[subtype](foundation-core.subtypes.md) of `X`, we get that dependent functions
of type `(t : 𝕊¹) → Σ (A t) (B t)` are exactly the
[fixpoints](synthetic-homotopy-theory.sections-descent-circle.md) of `e` which
belong to `R`.

## Properties

### Characterization of sections of families of subtypes

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : double-family-with-dependent-descent-data-circle l A l3)
  ( is-subtype-B :
    ( t : S) →
    is-subtype
      ( double-family-double-family-with-dependent-descent-data-circle A B t))
  where

  subtype-descent-data-circle-subtype :
    subtype l3 (type-family-with-descent-data-circle A)
  pr1 (subtype-descent-data-circle-subtype x) =
    type-double-family-with-dependent-descent-data-circle A B x
  pr2 (subtype-descent-data-circle-subtype x) =
    is-prop-equiv
      ( equiv-double-family-with-dependent-descent-data-circle A B x)
      ( is-subtype-B
        ( base-free-loop l)
        ( map-equiv-family-with-descent-data-circle A x))

  equiv-fixpoint-descent-data-circle-subtype-fixpoint-in-subtype :
    fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle
        ( family-with-descent-data-circle-dependent-pair-type l A B)) ≃
    ( Σ ( fixpoint-descent-data-circle
          ( descent-data-family-with-descent-data-circle A))
        ( λ x → is-in-subtype subtype-descent-data-circle-subtype (pr1 x)))
  equiv-fixpoint-descent-data-circle-subtype-fixpoint-in-subtype =
    equivalence-reasoning
    fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle
        ( family-with-descent-data-circle-dependent-pair-type l A B))
    ≃ Σ ( type-family-with-descent-data-circle A)
        ( λ x →
          Σ ( type-double-family-with-dependent-descent-data-circle A B x)
            ( λ r →
              map-Σ
                ( type-double-family-with-dependent-descent-data-circle A B)
                ( map-aut-family-with-descent-data-circle A)
                ( λ x →
                  map-dependent-automorphism-double-family-with-dependent-descent-data-circle
                    ( A)
                    ( B))
                ( x , r) ＝
              ( x , r)))
      by
        associative-Σ
          ( type-family-with-descent-data-circle A)
          ( type-double-family-with-dependent-descent-data-circle A B)
          ( λ u →
            map-Σ
              ( type-double-family-with-dependent-descent-data-circle A B)
              ( map-aut-family-with-descent-data-circle A)
              ( λ x →
                map-dependent-automorphism-double-family-with-dependent-descent-data-circle
                  ( A)
                  ( B))
              ( u) ＝
            u)
    ≃ Σ ( type-family-with-descent-data-circle A)
        ( λ x →
          ( is-in-subtype subtype-descent-data-circle-subtype x) ×
          ( map-aut-family-with-descent-data-circle A x ＝ x))
      by
        equiv-tot
          ( λ x →
            equiv-tot
              ( λ r →
                extensionality-type-subtype'
                  ( subtype-descent-data-circle-subtype)
                  ( _)
                  ( x , r)))
    ≃ Σ ( type-family-with-descent-data-circle A)
        ( λ x →
          ( map-aut-family-with-descent-data-circle A x ＝ x) ×
          ( is-in-subtype subtype-descent-data-circle-subtype x))
      by equiv-tot (λ _ → commutative-product)
    ≃ Σ ( fixpoint-descent-data-circle
          ( descent-data-family-with-descent-data-circle A))
        ( λ x → is-in-subtype subtype-descent-data-circle-subtype (pr1 x))
      by
        inv-associative-Σ
          ( type-family-with-descent-data-circle A)
          ( λ x → map-aut-family-with-descent-data-circle A x ＝ x)
          ( λ x → is-in-subtype subtype-descent-data-circle-subtype (pr1 x))

  equiv-section-descent-data-circle-subtype-fixpoint-in-subtype :
    dependent-universal-property-circle l →
    ( (x : S) → family-descent-data-circle-dependent-pair-type l A B x) ≃
    ( Σ ( fixpoint-descent-data-circle
          ( descent-data-family-with-descent-data-circle A))
        ( λ x → is-in-subtype subtype-descent-data-circle-subtype (pr1 x)))
  equiv-section-descent-data-circle-subtype-fixpoint-in-subtype dup-circle =
    equiv-fixpoint-descent-data-circle-subtype-fixpoint-in-subtype ∘e
    ( equiv-ev-fixpoint-descent-data-circle
      ( l)
      ( family-with-descent-data-circle-dependent-pair-type l A B)
      ( dup-circle))
```
