# Empty multisets

```agda
open import foundation.function-extensionality-axiom

module
  trees.empty-multisets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types funext
open import foundation.identity-types funext
open import foundation.propositions funext
open import foundation.universe-levels

open import trees.elementhood-relation-w-types funext
open import trees.multisets funext
open import trees.w-types funext
```

</details>

## Idea

A [multiset](trees.multisets.md) is said to be **empty** if it has no
[elements](trees.elementhood-relation-w-types.md).

## Definition

### The predicate of being an empty multiset

```agda
module _
  {l : Level}
  where

  is-empty-𝕍 : 𝕍 l → UU l
  is-empty-𝕍 (tree-𝕎 X Y) = is-empty X

  is-property-is-empty-𝕍 : (X : 𝕍 l) → is-prop (is-empty-𝕍 X)
  is-property-is-empty-𝕍 (tree-𝕎 X Y) = is-property-is-empty

  is-empty-prop-𝕍 : 𝕍 l → Prop l
  is-empty-prop-𝕍 X = is-empty-𝕍 X , is-property-is-empty-𝕍 X
```

### The predicate of being a multiset with no elements

However, note that this predicate returns a type of universe level `lsuc l`.

```agda
module _
  {l : Level}
  where

  has-no-elements-𝕍 : 𝕍 l → UU (lsuc l)
  has-no-elements-𝕍 X = (Y : 𝕍 l) → Y ∉-𝕎 X
```

## Properties

### A multiset `X` is empty if and only if it has no elements

```agda
module _
  {l : Level}
  where

  is-empty-has-no-elements-𝕍 :
    (X : 𝕍 l) → has-no-elements-𝕍 X → is-empty-𝕍 X
  is-empty-has-no-elements-𝕍 (tree-𝕎 X Y) H x = H (Y x) (x , refl)

  has-no-elements-is-empty-𝕍 :
    (X : 𝕍 l) → is-empty-𝕍 X → has-no-elements-𝕍 X
  has-no-elements-is-empty-𝕍 (tree-𝕎 X Y) H ._ (x , refl) = H x
```
