---
title: Dubuc-Penon compact types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.dubuc-penon-compact-types where

open import foundation.disjunction using (disj-Prop; type-disj-Prop)
open import foundation.propositions using
  ( Prop; Π-Prop; function-Prop; type-Prop)
open import foundation.subtypes using (subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

A type is said to be Dubuc-Penon compact if for every proposition `P` and every subtype `Q` of `X` such that `P ∨ Q x` holds for all `x`, then either `P` is true or `Q` contains every element of `X`.

## Definition

```agda
is-dubuc-penon-compact-Prop :
  {l : Level} (l1 l2 : Level) → UU l → Prop (l ⊔ lsuc l1 ⊔ lsuc l2)
is-dubuc-penon-compact-Prop l1 l2 X =
  Π-Prop
    ( Prop l1)
    ( λ P →
      Π-Prop
        ( subtype l2 X)
        ( λ Q →
          function-Prop
            ( (x : X) → type-disj-Prop P (Q x))
            ( disj-Prop P (Π-Prop X Q))))

is-dubuc-penon-compact :
  {l : Level} (l1 l2 : Level) → UU l → UU (l ⊔ lsuc l1 ⊔ lsuc l2)
is-dubuc-penon-compact l1 l2 X = type-Prop (is-dubuc-penon-compact-Prop l1 l2 X)
```
