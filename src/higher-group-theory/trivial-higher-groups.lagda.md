# Trivial higher groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module higher-group-theory.trivial-higher-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types funext univalence truncations
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.raising-universe-levels-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import higher-group-theory.higher-groups funext univalence truncations
```

</details>

## Idea

A [higher group](higher-group-theory.higher-groups.md) `G` is **trivial** if its
underlying type is contractible.

## Definitions

### Trivial higher groups

```agda
module _
  {l : Level} (G : ∞-Group l)
  where

  is-trivial-prop-∞-Group : Prop l
  is-trivial-prop-∞-Group = is-contr-Prop (type-∞-Group G)

  is-trivial-∞-Group : UU l
  is-trivial-∞-Group = type-Prop is-trivial-prop-∞-Group

  is-property-is-trivial-∞-Group : is-prop (is-trivial-∞-Group)
  is-property-is-trivial-∞-Group = is-prop-type-Prop is-trivial-prop-∞-Group
```

### Higher groups with contractible classifying type

```agda
module _
  {l : Level} (G : ∞-Group l)
  where

  has-contractible-classifying-type-prop-∞-Group : Prop l
  has-contractible-classifying-type-prop-∞-Group =
    is-contr-Prop (classifying-type-∞-Group G)

  has-contractible-classifying-type-∞-Group : UU l
  has-contractible-classifying-type-∞-Group =
    type-Prop has-contractible-classifying-type-prop-∞-Group

  is-property-has-contractible-classifying-type-∞-Group :
    is-prop (has-contractible-classifying-type-∞-Group)
  is-property-has-contractible-classifying-type-∞-Group =
    is-prop-type-Prop has-contractible-classifying-type-prop-∞-Group
```

### The trivial higher group

```agda
trivial-∞-Group : {l : Level} → ∞-Group l
pr1 (pr1 (trivial-∞-Group {l})) = raise-unit l
pr2 (pr1 trivial-∞-Group) = raise-star
pr2 (trivial-∞-Group {l}) =
  is-0-connected-is-contr (raise-unit l) is-contr-raise-unit

has-contractible-classifying-type-trivial-∞-Group :
  {l : Level} → has-contractible-classifying-type-∞-Group (trivial-∞-Group {l})
has-contractible-classifying-type-trivial-∞-Group = is-contr-raise-unit
```

## Properties

### Having contractible classifying type is equivalent to having contractible underlying type

This remains to be formalized.
