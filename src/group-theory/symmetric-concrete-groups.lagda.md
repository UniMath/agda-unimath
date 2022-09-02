---
title: Symmetric concrete groups
---

```agda
module group-theory.symmetric-concrete-groups where

open import foundation.sets
open import foundation.universe-levels

open import group-theory.automorphism-groups
open import group-theory.concrete-groups
```

## Idea

The symmetric concrete group of a set `X` is the connected component of the universe of sets at `X`.

## Definition

```agda
module _
  {l : Level} (X : UU-Set l)
  where

  symmetric-Concrete-Group : Concrete-Group (lsuc l)
  symmetric-Concrete-Group = Automorphism-Group (UU-Set l) X is-1-type-UU-Set
```
