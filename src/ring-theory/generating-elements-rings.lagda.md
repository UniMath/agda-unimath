# Generating elements of rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.generating-elements-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import group-theory.generating-elements-groups funext univalence truncations

open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

A **generating element** of a [ring](ring-theory.rings.md) `R` is an element `g`
which is a [generating element](group-theory.generating-elements-groups.md) of
the underlying additive [group](group-theory.groups.md) of `R`. That is, `g` is
a generating element of a ring `R` if for every element `x : R` there exists an
integer `k` such that `kg ＝ x`.

## Definitions

### Generating elements of a ring

```agda
module _
  {l : Level} (R : Ring l) (g : type-Ring R)
  where

  is-generating-element-prop-Ring : Prop l
  is-generating-element-prop-Ring =
    is-generating-element-prop-Group (group-Ring R) g
```
