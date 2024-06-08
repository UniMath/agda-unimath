# Mere equality

```agda
module foundation.mere-equality where

open import foundation-core.mere-equality public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.universe-levels

open import foundation-core.equivalence-relations
open import foundation-core.identity-types
open import foundation-core.sets
```

</details>

## Idea

Two elements in a type are said to be {{#concept "merely equal" Agda=mere-eq}} if there is an element of the
[propositionally truncated](foundation.propositional-truncations.md) [identity type](foundation-core.identity-types.md) between them.

## Properties

### Mere equality is an equivalence relation

```agda
mere-eq-equivalence-relation :
  {l1 : Level} (A : UU l1) → equivalence-relation l1 A
pr1 (mere-eq-equivalence-relation A) = mere-eq-Prop
pr1 (pr2 (mere-eq-equivalence-relation A)) = refl-mere-eq
pr1 (pr2 (pr2 (mere-eq-equivalence-relation A))) = symmetric-mere-eq
pr2 (pr2 (pr2 (mere-eq-equivalence-relation A))) = transitive-mere-eq
```

### Any map into a set reflects mere equality

```agda
module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : A → type-Set X)
  where

  reflects-mere-eq :
    reflects-equivalence-relation (mere-eq-equivalence-relation A) f
  reflects-mere-eq {x} {y} r =
    apply-universal-property-trunc-Prop r
      ( Id-Prop X (f x) (f y))
      ( ap f)

  reflecting-map-mere-eq :
    reflecting-map-equivalence-relation
      ( mere-eq-equivalence-relation A)
      ( type-Set X)
  pr1 reflecting-map-mere-eq = f
  pr2 reflecting-map-mere-eq = reflects-mere-eq
```
