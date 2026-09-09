# Strict complemented inequality on cardinals

```agda
module set-theory.strict-complemented-inequality-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.mere-decidable-embeddings
open import foundation.negation
open import foundation.nonsurjective-maps
open import foundation.projective-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.types-with-decidable-existential-quantifications
open import foundation.univalence
open import foundation.universe-levels

open import logic.de-morgan-maps
open import logic.propositional-double-negation-elimination
open import logic.propositionally-decidable-maps
open import logic.propositionally-decidable-types

open import set-theory.cardinals
open import set-theory.cardinals-with-decidable-existential-quantifications
open import set-theory.complemented-inequality-cardinals
open import set-theory.decidable-cardinals
open import set-theory.discrete-cardinals
open import set-theory.inequality-cardinals
open import set-theory.inhabited-cardinals
open import set-theory.projective-cardinals
open import set-theory.strict-indexed-inequality-cardinals
```

</details>

## Idea

We may say a [cardinal](set-theory.cardinals.md) `X` is (strictly)
{{#concept "complemented less than" Disambiguation="set-cardinal" Agda=le-complemented-Cardinal}}
a cardinal `Y`, written `X <ᵈ Y`, if `X ≤ᵈ Y` and `Y ≰ᵈ X`, in the sense that a
representative of `X` merely decidably embeds into a representative of `Y`, and
a representative of `Y` merely decidably embeds into a representative of `X`.

## Definitions

### Strict inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  le-complemented-prop-Cardinal :
    Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  le-complemented-prop-Cardinal X Y =
    product-Prop
      ( leq-complemented-prop-Cardinal X Y)
      ( neg-Prop (leq-complemented-prop-Cardinal Y X))

  le-complemented-Cardinal : Cardinal l1 → Cardinal l2 → UU (l1 ⊔ l2)
  le-complemented-Cardinal X Y = type-Prop (le-complemented-prop-Cardinal X Y)
```

### Strict inequality of cardinalities of sets

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  le-complemented-prop-cardinality : Prop (l1 ⊔ l2)
  le-complemented-prop-cardinality =
    le-complemented-prop-Cardinal (cardinality X) (cardinality Y)

  le-complemented-cardinality : UU (l1 ⊔ l2)
  le-complemented-cardinality =
    le-complemented-Cardinal (cardinality X) (cardinality Y)

  is-prop-le-complemented-cardinality : is-prop le-complemented-cardinality
  is-prop-le-complemented-cardinality =
    is-prop-type-Prop le-complemented-prop-cardinality
```

## Properties

### If `X <ⁱ Y` then `Y ≰ᵈ X`

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  not-geq-complemented-le-indexed-cardinality :
    le-indexed-cardinality X Y → ¬ leq-complemented-cardinality Y X
  not-geq-complemented-le-indexed-cardinality X<Y Y≤X =
    apply-twice-universal-property-trunc-Prop
      ( pr1 (inv-unit-le-indexed-cardinality X Y X<Y))
      ( inv-unit-leq-complemented-cardinality Y X Y≤X)
      ( empty-Prop)
      ( λ y₀ e →
        is-not-surjective-is-nonsurjective
          ( pr2 (inv-unit-le-indexed-cardinality X Y X<Y)
            ( map-retraction-map-decidable-emb y₀ e))
          ( is-surjective-has-section
            ( map-decidable-emb e ,
              is-retraction-map-retraction-map-decidable-emb y₀ e)))

  le-complemented-le-indexed-leq-complemented-cardinality :
    leq-complemented-cardinality X Y →
    le-indexed-cardinality X Y → le-complemented-cardinality X Y
  le-complemented-le-indexed-leq-complemented-cardinality X≤Y X<Y =
    ( X≤Y , not-geq-complemented-le-indexed-cardinality X<Y)
```

### Strict complemented inequality implies strict indexed inequality

If `Y` is projective, discrete, and has decidable existential quantifications,
then `X <ᵈ Y` implies `X <ⁱ Y`.

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  (is-projective-Y : is-projective-Level (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y : has-decidable-∃-bool (type-Set Y))
  where

  le-indexed-le-complemented-cardinality :
    le-complemented-cardinality X Y → le-indexed-cardinality X Y
  le-indexed-le-complemented-cardinality (X≤Y , nY≤X) =
    unit-le-indexed-cardinality X Y
      ( prop-double-negation-elim-is-inhabited-or-empty
          ( is-inhabited-or-empty-has-decidable-∃
            ( has-decidable-∃-has-decidable-∃-bool decidable-∃-Y))
          ( nY≤X ∘
            unit-leq-complemented-cardinality Y X ∘
            mere-decidable-emb-is-empty) ,
        λ f →
          rec-trunc-Prop
            ( is-nonsurjective-Prop f)
            ( λ e →
              is-nonsurjective-is-not-surjective-is-inhabited-or-empty-map-has-decidable-∃
                ( has-decidable-∃-has-decidable-∃-bool decidable-∃-Y)
                ( is-inhabited-or-empty-map-has-decidable-∃-Level
                  ( has-decidable-∃-decidable-emb
                    ( has-decidable-∃-has-decidable-∃-bool decidable-∃-Y) e)
                  decidable-equality-Y f)
                ( nY≤X ∘
                  unit-leq-complemented-cardinality Y X ∘
                  reverse-mere-decidable-emb-surjection-is-projective
                    ( has-decidable-equality-emb (emb-decidable-emb e)
                      decidable-equality-Y)
                    is-projective-Y ∘ pair f))
            ( inv-unit-leq-complemented-cardinality X Y X≤Y))

module _
  {l1 l2 : Level} (X : Cardinal l1) (Y : Cardinal l2)
  (is-projective-Y : is-projective-Cardinal (l1 ⊔ l2) Y)
  (is-discrete-Y : is-discrete-Cardinal Y)
  (decidable-∃-Y : has-decidable-∃-Cardinal Y)
  where

  le-indexed-le-complemented-Cardinal :
    le-complemented-Cardinal X Y →
    le-indexed-Cardinal X Y
  le-indexed-le-complemented-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( is-projective-Cardinal (l1 ⊔ l2) Y)
            ( function-Prop
              ( is-discrete-Cardinal Y)
              ( function-Prop
                ( has-decidable-∃-Cardinal Y)
                ( function-Prop
                  ( le-complemented-Cardinal X Y)
                  ( le-indexed-prop-Cardinal X Y))))))
      ( λ X Y pY dY hY →
        le-indexed-le-complemented-cardinality X Y
          ( inv-unit-is-projective-cardinality Y pY)
          ( inv-unit-is-discrete-cardinality Y dY)
          ( inv-unit-has-decidable-∃-cardinality Y hY))
      X Y is-projective-Y is-discrete-Y decidable-∃-Y

module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  (is-projective-Y : is-projective-Level (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y : has-decidable-∃-bool (type-Set Y))
  where

  le-complemented-iff-le-indexed-cardinality :
    leq-complemented-cardinality X Y →
    le-indexed-cardinality X Y ↔ le-complemented-cardinality X Y
  le-complemented-iff-le-indexed-cardinality X≤Y =
    ( le-complemented-le-indexed-leq-complemented-cardinality X Y X≤Y ,
      le-indexed-le-complemented-cardinality X Y
        is-projective-Y decidable-equality-Y decidable-∃-Y)

module _
  {l1 l2 : Level} (X : Cardinal l1) (Y : Cardinal l2)
  (is-projective-Y : is-projective-Cardinal (l1 ⊔ l2) Y)
  (is-discrete-Y : is-discrete-Cardinal Y)
  (decidable-∃-Y : has-decidable-∃-Cardinal Y)
  where

  le-complemented-iff-le-indexed-Cardinal :
    leq-complemented-Cardinal X Y →
    le-indexed-Cardinal X Y ↔ le-complemented-Cardinal X Y
  le-complemented-iff-le-indexed-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( is-projective-Cardinal (l1 ⊔ l2) Y)
            ( function-Prop
              ( is-discrete-Cardinal Y)
              ( function-Prop
                ( has-decidable-∃-Cardinal Y)
                ( function-Prop
                  ( leq-complemented-Cardinal X Y)
                  ( iff-Prop
                    ( le-indexed-prop-Cardinal X Y)
                    ( le-complemented-prop-Cardinal X Y)))))))
      ( λ X Y pY dY hY →
        le-complemented-iff-le-indexed-cardinality X Y
          ( inv-unit-is-projective-cardinality Y pY)
          ( inv-unit-is-discrete-cardinality Y dY)
          ( inv-unit-has-decidable-∃-cardinality Y hY))
      X Y is-projective-Y is-discrete-Y decidable-∃-Y
```
