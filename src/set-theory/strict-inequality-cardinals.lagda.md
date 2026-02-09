# Strict inequality on cardinals

```agda
module set-theory.strict-inequality-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-equality
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
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.mere-embeddings
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
open import foundation.types-with-decidable-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import logic.propositionally-decidable-types

open import set-theory.cardinals
open import set-theory.cardinals-with-merely-decidable-sums
open import set-theory.complemented-inequality-cardinals
open import set-theory.discrete-cardinals
open import set-theory.inequality-cardinals
open import set-theory.inhabited-cardinals
open import set-theory.projective-cardinals
open import set-theory.strict-indexed-inequality-cardinals
```

</details>

## Idea

We may say a [cardinal](set-theory.cardinals.md) `X` is (strictly)
{{#concept "less than" Disambiguation="set-cardinal" Agda=le-Cardinal}} a
cardinal `Y` if `X ≤ Y` and `Y ≰ X`, in the sense that every set in the
equivalence class of `X` merely embeds into every set in the equivalence class
of `Y`, and no set in the equivalence class of `Y` merely embeds into any set in
the equivalence class of `X`.

## Definition

### Strict inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  le-prop-Cardinal :
    Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  le-prop-Cardinal X Y =
    product-Prop
      ( leq-prop-Cardinal X Y)
      ( neg-Prop (leq-prop-Cardinal Y X))

  le-Cardinal : Cardinal l1 → Cardinal l2 → UU (l1 ⊔ l2)
  le-Cardinal X Y = type-Prop (le-prop-Cardinal X Y)
```

### Strict inequality of cardinalities of sets

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  le-prop-cardinality : Prop (l1 ⊔ l2)
  le-prop-cardinality =
    le-prop-Cardinal (cardinality X) (cardinality Y)

  le-cardinality : UU (l1 ⊔ l2)
  le-cardinality =
    le-Cardinal (cardinality X) (cardinality Y)

  is-prop-le-cardinality : is-prop le-cardinality
  is-prop-le-cardinality =
    is-prop-type-Prop le-prop-cardinality
```

## Properties

### If `Y` is inhabited-or-empty and `Y ≰ X` then `Y` is inhabited

```agda
module _
  {l1 l2 : Level}
  (X : Set l1) (Y : Set l2)
  (dY : is-inhabited-or-empty (type-Set Y))
  where

  is-inhabited-is-not-leq-cardinality :
    ¬ leq-cardinality Y X → is-inhabited (type-Set Y)
  is-inhabited-is-not-leq-cardinality H =
    rec-coproduct
      ( id)
      ( λ ny →
        ex-falso
          ( H ( unit-leq-cardinality Y X
                ( mere-emb-is-empty ny))))
      ( dY)
```

### Projective codomain implies surjections induce reverse embeddings

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  geq-is-surjective-cardinality :
    is-projective-Level' (l1 ⊔ l2) (type-Set Y) →
    (f : type-Set X → type-Set Y) →
    is-surjective f →
    leq-cardinality Y X
  geq-is-surjective-cardinality is-projective-Y f is-surjective-f =
    unit-leq-cardinality Y X
      ( map-trunc-Prop
        ( λ s →
          ( pr1 ∘ s ,
            is-emb-is-injective
              ( is-set-type-Set X)
              ( is-injective-has-retraction (pr1 ∘ s) f (pr2 ∘ s))))
        ( is-projective-Y (fiber f) is-surjective-f))
```

### Strict indexed inequality implies strict inequality under a forward embedding, assuming excluded middle

<!-- TODO: factor out non-LEM variant -->

```agda
module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  where

  not-geq-le-indexed-leq-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y →
    ¬ leq-cardinality Y X
  not-geq-le-indexed-leq-cardinality X≤Y X<Y Y≤X =
    rec-trunc-Prop
      ( empty-Prop)
      ( λ e →
        is-not-surjective-is-nonsurjective
          ( pr2
            ( inv-unit-le-indexed-cardinality X Y X<Y)
            ( map-equiv e))
          ( is-surjective-map-equiv e))
      ( antisymmetric-mere-emb
        ( lem)
        ( inv-unit-leq-cardinality X Y X≤Y)
        ( inv-unit-leq-cardinality Y X Y≤X))

  le-le-indexed-leq-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y →
    le-cardinality X Y
  le-le-indexed-leq-cardinality X≤Y X<Y =
    ( X≤Y , not-geq-le-indexed-leq-cardinality X≤Y X<Y)
```

### Strict inequality implies strict indexed inequality under projectivity

```agda
module _
  {l1 l2 : Level}
  (X : Set l1) (Y : Set l2)
  (is-projective-Y : is-projective-Level' (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-Σ-Y :
    type-trunc-Prop (has-decidable-Σ-Level (l1 ⊔ l2) (type-Set Y)))
  (decidable-Σ-X :
    type-trunc-Prop (has-decidable-Σ-Level l2 (type-Set X)))
  where

  le-indexed-le-cardinality :
    le-cardinality X Y →
    le-indexed-cardinality X Y
  le-indexed-le-cardinality (_ , nY≤X) =
    unit-le-indexed-cardinality X Y
      ( is-inhabited-is-not-leq-cardinality X Y
          ( is-inhabited-or-empty-merely-has-decidable-Σ-Level decidable-Σ-Y)
          ( nY≤X) ,
        λ f →
        rec-trunc-Prop
          ( is-nonsurjective-Prop f)
          ( λ hΣY →
            rec-trunc-Prop
              ( is-nonsurjective-Prop f)
              ( λ hΣX →
                is-nonsurjective-is-not-surjective-has-decidable-Σ-Level-is-inhabited-or-empty-map
                  hΣY
                  ( is-inhabited-or-empty-map-has-decidable-Σ-Level
                    hΣX decidable-equality-Y f)
                  ( nY≤X ∘
                    geq-is-surjective-cardinality X Y is-projective-Y f))
              ( decidable-Σ-X))
          ( decidable-Σ-Y))

module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  (is-projective-Y : is-projective-Level' (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-Σ-Y :
    type-trunc-Prop (has-decidable-Σ-Level (l1 ⊔ l2) (type-Set Y)))
  (decidable-Σ-X :
    type-trunc-Prop (has-decidable-Σ-Level l2 (type-Set X)))
  where

  le-iff-le-indexed-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y ↔ le-cardinality X Y
  le-iff-le-indexed-cardinality X≤Y =
    ( le-le-indexed-leq-cardinality lem X Y X≤Y ,
      le-indexed-le-cardinality X Y is-projective-Y
        decidable-equality-Y decidable-Σ-Y decidable-Σ-X)
```

### Strict inequality implies strict indexed inequality for projective cardinals

```agda
module _
  {l1 l2 : Level}
  where

  le-indexed-le-Cardinal :
    (X : Cardinal l1) (Y : Cardinal l2) →
    is-projective-Cardinal (l1 ⊔ l2) Y →
    is-discrete-Cardinal Y →
    merely-decidable-Σ-Cardinal (l1 ⊔ l2) Y →
    merely-decidable-Σ-Cardinal l2 X →
    le-Cardinal X Y →
    le-indexed-Cardinal X Y
  le-indexed-le-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( is-projective-Cardinal (l1 ⊔ l2) Y)
            ( function-Prop
              ( is-discrete-Cardinal Y)
              ( function-Prop
                ( merely-decidable-Σ-Cardinal (l1 ⊔ l2) Y)
                ( function-Prop
                  ( merely-decidable-Σ-Cardinal l2 X)
                  ( function-Prop
                    ( le-Cardinal X Y)
                    ( le-indexed-prop-Cardinal X Y)))))))
      ( λ X Y is-projective-Y is-discrete-Y merely-Σ-Y merely-Σ-X →
        le-indexed-le-cardinality
          ( X)
          ( Y)
          ( inv-unit-is-projective-cardinality Y is-projective-Y)
          ( inv-unit-is-discrete-cardinality Y is-discrete-Y)
          ( inv-unit-merely-decidable-Σ-cardinality Y merely-Σ-Y)
          ( inv-unit-merely-decidable-Σ-cardinality X merely-Σ-X))

  le-iff-le-indexed-Cardinal :
    (lem : level-LEM (l1 ⊔ l2)) →
    (X : Cardinal l1) (Y : Cardinal l2) →
    is-projective-Cardinal (l1 ⊔ l2) Y →
    is-discrete-Cardinal Y →
    merely-decidable-Σ-Cardinal (l1 ⊔ l2) Y →
    merely-decidable-Σ-Cardinal l2 X →
    leq-Cardinal X Y →
    le-indexed-Cardinal X Y ↔ le-Cardinal X Y
  le-iff-le-indexed-Cardinal lem =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( is-projective-Cardinal (l1 ⊔ l2) Y)
            ( function-Prop
              ( is-discrete-Cardinal Y)
              ( function-Prop
                ( merely-decidable-Σ-Cardinal (l1 ⊔ l2) Y)
                ( function-Prop
                  ( merely-decidable-Σ-Cardinal l2 X)
                  ( function-Prop
                    ( leq-Cardinal X Y)
                    ( iff-Prop
                      ( le-indexed-prop-Cardinal X Y)
                      ( le-prop-Cardinal X Y))))))))
      ( λ X Y is-projective-Y is-discrete-Y merely-Σ-Y merely-Σ-X →
        le-iff-le-indexed-cardinality
          ( lem)
          ( X)
          ( Y)
          ( inv-unit-is-projective-cardinality Y is-projective-Y)
          ( inv-unit-is-discrete-cardinality Y is-discrete-Y)
          ( inv-unit-merely-decidable-Σ-cardinality Y merely-Σ-Y)
          ( inv-unit-merely-decidable-Σ-cardinality X merely-Σ-X))
```
