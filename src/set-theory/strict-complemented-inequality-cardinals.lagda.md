# Strict complemented inequality on cardinals

```agda
{-# OPTIONS --lossy-unification #-}

module set-theory.strict-complemented-inequality-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
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
open import foundation.types-with-decidable-existential-quantification
open import foundation.univalence
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import logic.de-morgan-maps
open import logic.propositionally-decidable-maps
open import logic.propositionally-decidable-types

open import set-theory.cardinals
open import set-theory.cardinals-with-decidable-existential-quantification
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
a cardinal `Y` if `X ≤ᵈ Y` and `Y ≰ᵈ X`, in the sense that every set in the
equivalence class of `X` merely decidably embeds into every set in the
equivalence class of `Y` via a decidable embedding, and no set in the
equivalence class of `Y` merely embeds into any set in the equivalence class of
`X` via a decidable embedding.

## Definition

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

### If `Y` is inhabited-or-empty and `Y ≰ X` then `Y` is inhabited

```agda
module _
  {l1 l2 : Level}
  (X : Set l1) (Y : Set l2)
  (dY : is-inhabited-or-empty (type-Set Y))
  where

  is-inhabited-is-not-leq-complemented-cardinality :
    ¬ leq-complemented-cardinality Y X → is-inhabited (type-Set Y)
  is-inhabited-is-not-leq-complemented-cardinality H =
    rec-coproduct
      ( id)
      ( λ ny →
        ex-falso
          ( H ( unit-leq-complemented-cardinality Y X
                ( mere-decidable-emb-is-empty ny))))
      ( dY)
```

### Projective codomain with decidable equality implies surjections induce reverse decidable embeddings

```agda
module _
  {l1 l2 : Level}
  (X : Set l1) (Y : Set l2)
  (dX : has-decidable-equality (type-Set X))
  where

  geq-complemented-is-surjective-cardinality :
    is-projective-Level (l1 ⊔ l2) (type-Set Y) →
    (f : type-Set X → type-Set Y) →
    is-surjective f →
    leq-complemented-cardinality Y X
  geq-complemented-is-surjective-cardinality is-projective-Y f is-surjective-f =
    unit-leq-complemented-cardinality Y X
      ( map-trunc-Prop
        ( λ s →
          let
            g = pr1 ∘ s
            inj = is-injective-has-retraction g f (pr2 ∘ s)
          in
          ( g ,
            ( is-emb-is-injective (is-set-type-Set X) inj ,
              is-decidable-map-retraction dX g (f , pr2 ∘ s))))
        ( is-projective-Y (fiber f) is-surjective-f))
```

### Strict indexed inequality implies strict inequality under a forward embedding, assuming WLPO

```agda
module _
  {l1 l2 : Level}
  (wlpo : level-WLPO (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  where

  not-geq-complemented-le-indexed-leq-complemented-cardinality :
    leq-complemented-cardinality X Y →
    le-indexed-cardinality X Y →
    ¬ leq-complemented-cardinality Y X
  not-geq-complemented-le-indexed-leq-complemented-cardinality X≤Y X<Y Y≤X =
    rec-trunc-Prop
      ( empty-Prop)
      ( λ e →
        is-not-surjective-is-nonsurjective
          ( pr2
            ( inv-unit-le-indexed-cardinality X Y X<Y)
            ( map-equiv e))
          ( is-surjective-map-equiv e))
      ( antisymmetric-mere-decidable-emb
        ( wlpo)
        ( inv-unit-leq-complemented-cardinality X Y X≤Y)
        ( inv-unit-leq-complemented-cardinality Y X Y≤X))

  le-complemented-le-indexed-leq-complemented-cardinality :
    leq-complemented-cardinality X Y →
    le-indexed-cardinality X Y →
    le-complemented-cardinality X Y
  le-complemented-le-indexed-leq-complemented-cardinality X≤Y X<Y =
    ( X≤Y ,
      not-geq-complemented-le-indexed-leq-complemented-cardinality X≤Y X<Y)
```

### Strict inequality implies strict indexed inequality under projectivity

```agda
module _
  {l1 l2 : Level}
  (X : Set l1) (Y : Set l2)
  (decidable-equality-X : has-decidable-equality (type-Set X))
  (decidable-∃-X :
    type-trunc-Prop (has-decidable-∃-Level l2 (type-Set X)))
  (is-projective-Y : is-projective-Level (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y :
    type-trunc-Prop (has-decidable-∃-Level (l1 ⊔ l2) (type-Set Y)))
  where

  le-indexed-le-complemented-cardinality :
    le-complemented-cardinality X Y →
    le-indexed-cardinality X Y
  le-indexed-le-complemented-cardinality (_ , nY≤X) =
    unit-le-indexed-cardinality X Y
      ( is-inhabited-is-not-leq-complemented-cardinality X Y
          ( is-inhabited-or-empty-merely-has-decidable-∃-Level decidable-∃-Y)
          ( nY≤X) ,
        λ f →
          apply-twice-universal-property-trunc-Prop
            decidable-∃-Y
            decidable-∃-X
            ( is-nonsurjective-Prop f)
            ( λ hΣY hΣX →
              is-nonsurjective-is-not-surjective-has-decidable-∃-is-inhabited-or-empty-map
                hΣY
                ( is-inhabited-or-empty-map-has-decidable-∃-Level
                  hΣX decidable-equality-Y f)
                ( nY≤X ∘
                  geq-complemented-is-surjective-cardinality
                    X Y
                    decidable-equality-X
                    is-projective-Y f)
            )
      )

module _
  {l1 l2 : Level}
  (wlpo : level-WLPO (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  (decidable-equality-X : has-decidable-equality (type-Set X))
  (decidable-∃-X :
    type-trunc-Prop (has-decidable-∃-Level l2 (type-Set X)))
  (is-projective-Y : is-projective-Level (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y :
    type-trunc-Prop (has-decidable-∃-Level (l1 ⊔ l2) (type-Set Y)))
  where

  le-complemented-iff-le-indexed-cardinality :
    leq-complemented-cardinality X Y →
    le-indexed-cardinality X Y ↔ le-complemented-cardinality X Y
  le-complemented-iff-le-indexed-cardinality X≤Y =
    ( le-complemented-le-indexed-leq-complemented-cardinality wlpo X Y X≤Y ,
      le-indexed-le-complemented-cardinality X Y
        ( decidable-equality-X)
        ( decidable-∃-X)
        ( is-projective-Y)
        ( decidable-equality-Y)
        ( decidable-∃-Y))
```

### Strict inequality implies strict indexed inequality for projective cardinals

```agda
module _
  {l1 l2 : Level}
  where

  le-indexed-le-complemented-Cardinal :
    (X : Cardinal l1) (Y : Cardinal l2) →
    is-discrete-Cardinal X →
    merely-decidable-∃-Cardinal l2 X →
    is-projective-Cardinal (l1 ⊔ l2) Y →
    is-discrete-Cardinal Y →
    merely-decidable-∃-Cardinal (l1 ⊔ l2) Y →
    le-complemented-Cardinal X Y →
    le-indexed-Cardinal X Y
  le-indexed-le-complemented-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( is-discrete-Cardinal X)
            ( function-Prop
              ( merely-decidable-∃-Cardinal l2 X)
              ( function-Prop
                ( is-projective-Cardinal (l1 ⊔ l2) Y)
                ( function-Prop
                  ( is-discrete-Cardinal Y)
                  ( function-Prop
                    ( merely-decidable-∃-Cardinal (l1 ⊔ l2) Y)
                    ( function-Prop
                      ( le-complemented-Cardinal X Y)
                      ( le-indexed-prop-Cardinal X Y))))))))
      ( λ X Y
          is-discrete-X merely-Σ-X
          is-projective-Y is-discrete-Y merely-Σ-Y →
        le-indexed-le-complemented-cardinality
          ( X)
          ( Y)
          ( inv-unit-is-discrete-cardinality X is-discrete-X)
          ( inv-unit-merely-decidable-∃-cardinality X merely-Σ-X)
          ( inv-unit-is-projective-cardinality Y is-projective-Y)
          ( inv-unit-is-discrete-cardinality Y is-discrete-Y)
          ( inv-unit-merely-decidable-∃-cardinality Y merely-Σ-Y))

  le-complemented-iff-le-indexed-Cardinal :
    (wlpo : level-WLPO (l1 ⊔ l2)) →
    (X : Cardinal l1) (Y : Cardinal l2) →
    is-discrete-Cardinal X →
    merely-decidable-∃-Cardinal l2 X →
    is-projective-Cardinal (l1 ⊔ l2) Y →
    is-discrete-Cardinal Y →
    merely-decidable-∃-Cardinal (l1 ⊔ l2) Y →
    leq-complemented-Cardinal X Y →
    le-indexed-Cardinal X Y ↔ le-complemented-Cardinal X Y
  le-complemented-iff-le-indexed-Cardinal wlpo =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( is-discrete-Cardinal X)
            ( function-Prop
              ( merely-decidable-∃-Cardinal l2 X)
              ( function-Prop
                ( is-projective-Cardinal (l1 ⊔ l2) Y)
                ( function-Prop
                  ( is-discrete-Cardinal Y)
                  ( function-Prop
                    ( merely-decidable-∃-Cardinal (l1 ⊔ l2) Y)
                    ( function-Prop
                      ( leq-complemented-Cardinal X Y)
                      ( iff-Prop
                        ( le-indexed-prop-Cardinal X Y)
                        ( le-complemented-prop-Cardinal X Y)))))))))
      ( λ X Y
          is-discrete-X merely-Σ-X
          is-projective-Y is-discrete-Y merely-Σ-Y →
        le-complemented-iff-le-indexed-cardinality
          ( wlpo)
          ( X)
          ( Y)
          ( inv-unit-is-discrete-cardinality X is-discrete-X)
          ( inv-unit-merely-decidable-∃-cardinality X merely-Σ-X)
          ( inv-unit-is-projective-cardinality Y is-projective-Y)
          ( inv-unit-is-discrete-cardinality Y is-discrete-Y)
          ( inv-unit-merely-decidable-∃-cardinality Y merely-Σ-Y))
```
