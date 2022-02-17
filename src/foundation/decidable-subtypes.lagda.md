# Decidable subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.decidable-subtypes where

open import foundation.decidable-propositions using
  ( decidable-Prop; prop-decidable-Prop; is-decidable-type-decidable-Prop;
    type-decidable-Prop)
open import foundation.decidable-types using (is-decidable)
open import foundation.propositions using (type-Prop)
open import foundation.subtypes using (subtype; type-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

A decidable subtype of a type consists of a family of decidable propositions over it.

## Definitions

### Decidable subtypes

```agda
is-decidable-subtype : {l1 l2 : Level} {A : UU l1} → subtype l2 A → UU (l1 ⊔ l2)
is-decidable-subtype {A = A} P = (a : A) → is-decidable (type-Prop (P a))

decidable-subtype : {l1 : Level} (l : Level) (X : UU l1) → UU (l1 ⊔ lsuc l)
decidable-subtype l X = X → decidable-Prop l
```

### The underlying subtype of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where
  
  subtype-decidable-subtype : (P : decidable-subtype l2 A) → subtype l2 A
  subtype-decidable-subtype P a = prop-decidable-Prop (P a)

  is-decidable-subtype-subtype-decidable-subtype :
    (P : decidable-subtype l2 A) →
    is-decidable-subtype (subtype-decidable-subtype P)
  is-decidable-subtype-subtype-decidable-subtype P a =
    is-decidable-type-decidable-Prop (P a)

  type-prop-decidable-subtype : (P : decidable-subtype l2 A) → A → UU l2
  type-prop-decidable-subtype P a = type-decidable-Prop (P a)
```

### The underlying type of a decidable subtype

```agda
type-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A) → UU (l1 ⊔ l2)
type-decidable-subtype P = type-subtype (subtype-decidable-subtype P)
```
