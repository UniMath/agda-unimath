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
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-maps
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
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.mere-embeddings
open import foundation.negation
open import foundation.nonsurjective-maps
open import foundation.projective-types
open import foundation.propositional-extensionality
open import foundation.propositional-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.types-with-decidable-existential-quantifications
open import foundation.univalence
open import foundation.universe-levels

open import logic.propositional-double-negation-elimination
open import logic.propositionally-decidable-types

open import set-theory.cardinals
open import set-theory.cardinals-with-decidable-existential-quantifications
open import set-theory.complemented-inequality-cardinals
open import set-theory.discrete-cardinals
open import set-theory.inequality-cardinals
open import set-theory.inhabited-cardinals
open import set-theory.projective-cardinals
open import set-theory.strict-complemented-inequality-cardinals
open import set-theory.strict-indexed-inequality-cardinals
```

</details>

## Idea

We may say a [cardinal](set-theory.cardinals.md) `X` is (strictly)
{{#concept "less than" Disambiguation="set-cardinal" Agda=le-Cardinal}} a
cardinal `Y`, written `X < Y`, if `X ≤ Y` and `Y ≰ X`, in the sense that a
representative of `X` merely embeds into a representative of `Y`, and a
representative of `Y` does not merely embed into a representative of `X`.

## Definition

### Strict inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  le-prop-Cardinal :
    Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  le-prop-Cardinal X Y =
    product-Prop (leq-prop-Cardinal X Y) (neg-Prop (leq-prop-Cardinal Y X))

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

### If every embedding from `Y` to `X` is decidable, and `X <ⁱ Y`, then `Y ≰ X`

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  not-geq-le-indexed-cardinality-is-decidable-embeddings :
    ((e : type-Set Y ↪ type-Set X) → is-decidable-map (map-emb e)) →
    le-indexed-cardinality X Y → ¬ leq-cardinality Y X
  not-geq-le-indexed-cardinality-is-decidable-embeddings d X<Y Y≤X =
    not-geq-complemented-le-indexed-cardinality X Y X<Y
      ( unit-leq-complemented-cardinality Y X
        ( map-trunc-Prop
          ( λ e → (map-emb e , (is-emb-map-emb e , d e)))
          ( inv-unit-leq-cardinality Y X Y≤X)))
```

### Strict indexed inequality implies strict inequality under excluded middle

```agda
module _
  {l1 l2 : Level} (lem : level-LEM (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  where

  not-geq-le-indexed-cardinality-LEM :
    le-indexed-cardinality X Y → ¬ leq-cardinality Y X
  not-geq-le-indexed-cardinality-LEM =
    not-geq-le-indexed-cardinality-is-decidable-embeddings X Y
      ( λ e x → lem (fiber (map-emb e) x , is-prop-map-emb e x))

  le-le-indexed-leq-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y → le-cardinality X Y
  le-le-indexed-leq-cardinality X≤Y X<Y =
    ( X≤Y , not-geq-le-indexed-cardinality-LEM X<Y)
```

### Decidable existential quantification makes embeddings decidable

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  (decidable-equality-X : has-decidable-equality (type-Set X))
  (decidable-∃-Y : has-decidable-∃-bool (type-Set Y))
  where

  not-geq-le-indexed-cardinality-has-decidable-∃ :
    le-indexed-cardinality X Y → ¬ leq-cardinality Y X
  not-geq-le-indexed-cardinality-has-decidable-∃ =
    not-geq-le-indexed-cardinality-is-decidable-embeddings X Y
      ( is-decidable-map-emb-has-decidable-∃
        decidable-∃-Y decidable-equality-X)

  le-le-indexed-leq-cardinality-has-decidable-∃ :
    leq-cardinality X Y →
    le-indexed-cardinality X Y → le-cardinality X Y
  le-le-indexed-leq-cardinality-has-decidable-∃ X≤Y X<Y =
    ( X≤Y , not-geq-le-indexed-cardinality-has-decidable-∃ X<Y)
```

### Strict inequality implies strict indexed inequality under projectivity

If `X < Y` and `X` and `Y` have decidable existential quantification and `Y` is
projective and discrete, then `X <ⁱ Y`.

```agda
module _
  {l1 l2 : Level}
  (X : Set l1) (Y : Set l2)
  (decidable-∃-X : has-decidable-∃-bool (type-Set X))
  (is-projective-Y : is-projective-Level (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y : has-decidable-∃-bool (type-Set Y))
  where

  le-indexed-le-cardinality :
    le-cardinality X Y →
    le-indexed-cardinality X Y
  le-indexed-le-cardinality (_ , nY≤X) =
    unit-le-indexed-cardinality X Y
      ( is-inhabited-not-mere-emb
          ( prop-double-negation-elim-is-inhabited-or-empty
            ( is-inhabited-or-empty-has-decidable-∃
              ( has-decidable-∃-has-decidable-∃-bool decidable-∃-Y)))
          ( nY≤X ∘ unit-leq-cardinality Y X) ,
        λ f →
          is-nonsurjective-is-not-surjective-is-inhabited-or-empty-map-has-decidable-∃
            ( has-decidable-∃-has-decidable-∃-bool decidable-∃-Y)
            ( is-inhabited-or-empty-map-has-decidable-∃-Level
              ( has-decidable-∃-has-decidable-∃-bool decidable-∃-X)
              decidable-equality-Y f)
            ( nY≤X ∘
              unit-leq-cardinality Y X ∘
              reverse-mere-emb-surjection-is-projective
                is-projective-Y (is-set-type-Set X) ∘ pair f))

module _
  {l1 l2 : Level} (X : Cardinal l1) (Y : Cardinal l2)
  (decidable-∃-X : has-decidable-∃-Cardinal X)
  (is-projective-Y : is-projective-Cardinal (l1 ⊔ l2) Y)
  (is-discrete-Y : is-discrete-Cardinal Y)
  (decidable-∃-Y : has-decidable-∃-Cardinal Y)
  where

  le-indexed-le-Cardinal :
    le-Cardinal X Y →
    le-indexed-Cardinal X Y
  le-indexed-le-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( has-decidable-∃-Cardinal X)
            ( function-Prop
              ( is-projective-Cardinal (l1 ⊔ l2) Y)
              ( function-Prop
                ( is-discrete-Cardinal Y)
                ( function-Prop
                  ( has-decidable-∃-Cardinal Y)
                  ( function-Prop
                    ( le-Cardinal X Y)
                    ( le-indexed-prop-Cardinal X Y)))))))
      ( λ X Y hX pY dY hY →
        le-indexed-le-cardinality X Y
          ( inv-unit-has-decidable-∃-cardinality X hX)
          ( inv-unit-is-projective-cardinality Y pY)
          ( inv-unit-is-discrete-cardinality Y dY)
          ( inv-unit-has-decidable-∃-cardinality Y hY))
      X Y decidable-∃-X is-projective-Y is-discrete-Y decidable-∃-Y
```

Assuming excluded middle, we only need `Y` to be projective.

```agda
module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  (is-projective-Y : is-projective-Level (l1 ⊔ l2) (type-Set Y))
  where

  le-indexed-le-cardinality-LEM :
    le-cardinality X Y →
    le-indexed-cardinality X Y
  le-indexed-le-cardinality-LEM (_ , nY≤X) =
    unit-le-indexed-cardinality X Y
      ( is-inhabited-not-mere-emb
          ( prop-double-negation-elim-is-inhabited-or-empty
            ( is-inhabited-or-empty-LEM {l2 = l1} lem))
          ( nY≤X ∘ unit-leq-cardinality Y X) ,
        λ f →
        is-nonsurjective-is-not-surjective-LEM
          ( lem)
          ( nY≤X ∘
            unit-leq-cardinality Y X ∘
            reverse-mere-emb-surjection-is-projective
              is-projective-Y (is-set-type-Set X) ∘ pair f))

  le-iff-le-indexed-cardinality-LEM :
    leq-cardinality X Y →
    le-indexed-cardinality X Y ↔ le-cardinality X Y
  le-iff-le-indexed-cardinality-LEM X≤Y =
    ( le-le-indexed-leq-cardinality lem X Y X≤Y ,
      le-indexed-le-cardinality-LEM)

module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (X : Cardinal l1) (Y : Cardinal l2)
  (is-projective-Y : is-projective-Cardinal (l1 ⊔ l2) Y)
  where

  le-iff-le-indexed-Cardinal-LEM :
    leq-Cardinal X Y →
    le-indexed-Cardinal X Y ↔ le-Cardinal X Y
  le-iff-le-indexed-Cardinal-LEM =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( is-projective-Cardinal (l1 ⊔ l2) Y)
            ( function-Prop
              ( leq-Cardinal X Y)
              ( iff-Prop
                ( le-indexed-prop-Cardinal X Y)
                ( le-prop-Cardinal X Y)))))
      ( λ X Y pY →
        le-iff-le-indexed-cardinality-LEM lem X Y
          ( inv-unit-is-projective-cardinality Y pY))
      X Y is-projective-Y
```

### Strict and indexed strict inequality agree for projective discrete codomains

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  (decidable-∃-X : has-decidable-∃-bool (type-Set X))
  (is-projective-Y : is-projective-Level (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y : has-decidable-∃-bool (type-Set Y))
  where

  le-iff-le-indexed-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y ↔ le-cardinality X Y
  le-iff-le-indexed-cardinality X≤Y =
    ( ( λ X<Y →
        X≤Y ,
        ( λ Y≤X →
          rec-trunc-Prop empty-Prop
            ( λ e →
              not-geq-le-indexed-cardinality-has-decidable-∃ X Y
                ( has-decidable-equality-emb e decidable-equality-Y)
                ( decidable-∃-Y)
                X<Y Y≤X)
            ( inv-unit-leq-cardinality X Y X≤Y))) ,
      le-indexed-le-cardinality X Y decidable-∃-X
        is-projective-Y decidable-equality-Y decidable-∃-Y)

module _
  {l1 l2 : Level} (X : Cardinal l1) (Y : Cardinal l2)
  (decidable-∃-X : has-decidable-∃-Cardinal X)
  (is-projective-Y : is-projective-Cardinal (l1 ⊔ l2) Y)
  (is-discrete-Y : is-discrete-Cardinal Y)
  (decidable-∃-Y : has-decidable-∃-Cardinal Y)
  where

  le-iff-le-indexed-Cardinal :
    leq-Cardinal X Y →
    le-indexed-Cardinal X Y ↔ le-Cardinal X Y
  le-iff-le-indexed-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( has-decidable-∃-Cardinal X)
            ( function-Prop
              ( is-projective-Cardinal (l1 ⊔ l2) Y)
              ( function-Prop
                ( is-discrete-Cardinal Y)
                ( function-Prop
                  ( has-decidable-∃-Cardinal Y)
                  ( function-Prop
                    ( leq-Cardinal X Y)
                    ( iff-Prop
                      ( le-indexed-prop-Cardinal X Y)
                      ( le-prop-Cardinal X Y))))))))
      ( λ X Y hX pY dY hY →
        le-iff-le-indexed-cardinality X Y
          ( inv-unit-has-decidable-∃-cardinality X hX)
          ( inv-unit-is-projective-cardinality Y pY)
          ( inv-unit-is-discrete-cardinality Y dY)
          ( inv-unit-has-decidable-∃-cardinality Y hY))
      X Y decidable-∃-X is-projective-Y is-discrete-Y decidable-∃-Y
```
