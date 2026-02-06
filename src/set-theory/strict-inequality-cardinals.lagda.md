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
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinals
open import set-theory.complemented-inequality-cardinals
open import set-theory.inequality-cardinals
open import set-theory.inhabited-cardinals
open import set-theory.strict-indexed-inequality-cardinals
```

</details>

## Idea

We may say a [cardinal](set-theory.cardinals.md) `X` is (strictly)
{{#concept "less than" Disambiguation="set-cardinal" Agda=le-Cardinal}} a
cardinal `Y` if `X ≤ Y` and `Y ≰ X`.

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

### Under excluded middle, if `Y ≰ X` then `Y` is inhabited

```agda
module _
  {l1 l2 : Level}
  (lem : level-LEM l2)
  (X : Set l1) (Y : Set l2)
  where

  is-inhabited-is-not-leq-cardinality-LEM :
    ¬ leq-cardinality Y X → is-inhabited (type-Set Y)
  is-inhabited-is-not-leq-cardinality-LEM H =
    rec-coproduct
      ( id)
      ( λ ny →
        ex-falso
          ( H ( unit-leq-cardinality Y X
                ( mere-emb-is-empty (is-empty-type-trunc-Prop' ny)))))
      ( lem (is-inhabited-Prop (type-Set Y)))
```

### Projective codomain implies surjections induce reverse embeddings

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  leq-cardinality-is-surjective-map :
    is-projective-Level' (l1 ⊔ l2) (type-Set Y) →
    (f : type-Set X → type-Set Y) →
    is-surjective f →
    leq-cardinality Y X
  leq-cardinality-is-surjective-map is-projective-Y f is-surjective-f =
    unit-leq-cardinality Y X
      ( map-trunc-Prop
        ( λ s →
          ( pr1 ∘ s ,
            is-emb-is-injective
              ( is-set-type-Set X)
              ( is-injective-has-retraction (pr1 ∘ s) f (pr2 ∘ s))))
        ( is-projective-Y (fiber f) is-surjective-f))
```

### Strict indexed inequality implies strict inequality under a forward embedding

```agda
module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  where

  not-leq-right-le-indexed-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y →
    ¬ leq-cardinality Y X
  not-leq-right-le-indexed-cardinality X≤Y X<Y Y≤X =
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

  le-cardinality-le-indexed-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y →
    le-cardinality X Y
  le-cardinality-le-indexed-cardinality X≤Y X<Y =
    ( X≤Y , not-leq-right-le-indexed-cardinality X≤Y X<Y)
```

### Strict inequality implies strict indexed inequality under projectivity

```agda
module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (lem-l2 : level-LEM l2)
  (X : Set l1) (Y : Set l2)
  where

  le-indexed-cardinality-le-cardinality :
    is-projective-Level' (l1 ⊔ l2) (type-Set Y) →
    le-cardinality X Y →
    le-indexed-cardinality X Y
  le-indexed-cardinality-le-cardinality
    is-projective-Y (_ , nY≤X) =
    unit-le-indexed-cardinality X Y
      ( is-inhabited-is-not-leq-cardinality-LEM lem-l2 X Y nY≤X ,
        λ f →
        is-nonsurjective-is-not-surjective-LEM lem
          ( λ is-surjective-f →
            nY≤X
              ( leq-cardinality-is-surjective-map X Y
                ( is-projective-Y)
                ( f)
                ( is-surjective-f))))

  strict-inequality-iff-le-indexed-cardinality :
    is-projective-Level' (l1 ⊔ l2) (type-Set Y) →
    leq-cardinality X Y →
    le-indexed-cardinality X Y ↔ le-cardinality X Y
  strict-inequality-iff-le-indexed-cardinality is-projective-Y X≤Y =
    ( le-cardinality-le-indexed-cardinality lem X Y X≤Y ,
      le-indexed-cardinality-le-cardinality is-projective-Y)
```
