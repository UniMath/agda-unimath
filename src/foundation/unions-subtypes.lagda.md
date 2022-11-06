---
title: Union of subtypes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.unions-subtypes where

open import foundation.disjunction using (disj-Prop; disj-decidable-Prop)
open import foundation.decidable-subtypes using (decidable-subtype)
open import foundation.existential-quantification using (exists-Prop)
open import foundation.subtypes using (subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The union of two subtypes `A` and `B` is the subtype that contains the elements that are in `A` or in `B`.

## Definition

### Unions of subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  union-subtype : subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  union-subtype P Q x = disj-Prop (P x) (Q x)
```

### Unions of decidable subtypes

```agda
  union-decidable-subtype : decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  union-decidable-subtype P Q x = disj-decidable-Prop (P x) (Q x)
```

### Unions of families of subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  union-fam-subtype :
    {I : UU l2} (A : I → subtype l3 X) → subtype (l2 ⊔ l3) X
  union-fam-subtype {I} A x = exists-Prop I (λ i → A i x)
```
