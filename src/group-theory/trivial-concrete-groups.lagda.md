# Trivial concrete groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.trivial-concrete-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.raising-universe-levels-unit-type
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.concrete-groups funext univalence truncations

open import higher-group-theory.trivial-higher-groups funext univalence truncations
```

</details>

## Idea

A [concrete group](group-theory.concrete-groups.md) `G` is **trivial** if its
classifying type is contractible.

## Definitions

### Trivial higher groups

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  is-trivial-prop-Concrete-Group : Prop l
  is-trivial-prop-Concrete-Group =
    is-trivial-prop-∞-Group (∞-group-Concrete-Group G)

  is-trivial-Concrete-Group : UU l
  is-trivial-Concrete-Group = type-Prop is-trivial-prop-Concrete-Group

  is-property-is-trivial-Concrete-Group : is-prop (is-trivial-Concrete-Group)
  is-property-is-trivial-Concrete-Group =
    is-prop-type-Prop is-trivial-prop-Concrete-Group
```

### Higher groups with contractible classifying type

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  has-contractible-classifying-type-prop-Concrete-Group : Prop l
  has-contractible-classifying-type-prop-Concrete-Group =
    has-contractible-classifying-type-prop-∞-Group (∞-group-Concrete-Group G)

  has-contractible-classifying-type-Concrete-Group : UU l
  has-contractible-classifying-type-Concrete-Group =
    type-Prop has-contractible-classifying-type-prop-Concrete-Group

  is-property-has-contractible-classifying-type-Concrete-Group :
    is-prop (has-contractible-classifying-type-Concrete-Group)
  is-property-has-contractible-classifying-type-Concrete-Group =
    is-prop-type-Prop has-contractible-classifying-type-prop-Concrete-Group
```

### The trivial concrete group

```agda
trivial-Concrete-Group : {l : Level} → Concrete-Group l
pr1 trivial-Concrete-Group = trivial-∞-Group
pr2 trivial-Concrete-Group =
  is-trunc-is-contr (one-𝕋) (is-contr-raise-unit) (raise-star) (raise-star)

has-contractible-classifying-type-trivial-Concrete-Group :
  {l : Level} →
  has-contractible-classifying-type-Concrete-Group (trivial-Concrete-Group {l})
has-contractible-classifying-type-trivial-Concrete-Group =
  has-contractible-classifying-type-trivial-∞-Group
```

## Properties

### Having contractible classifying type is equivalent to having contractible underlying type

This remains to be formalized.
