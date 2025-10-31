# Generating elements of rings

```agda
module ring-theory.generating-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.generating-elements-groups

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "generating element" Disambiguation="of a ring" Agda=is-generating-element-prop-Ring}}
of a [ring](ring-theory.rings.md) `R` is an element `g` which is a
[generating element](group-theory.generating-elements-groups.md) of the
underlying additive [group](group-theory.groups.md) of `R`. That is, `g` is a
generating element of a ring `R` if for every element `x : R` there exists an
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
