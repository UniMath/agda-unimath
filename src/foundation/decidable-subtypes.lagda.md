# Decidable subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.decidable-subtypes where

open import foundation.coproduct-types using
  ( coprod; inl; inr; is-left; is-right; is-prop-is-left; is-prop-is-right)
open import foundation.decidable-propositions using
  ( decidable-Prop; prop-decidable-Prop; is-decidable-type-decidable-Prop;
    type-decidable-Prop; is-prop-type-decidable-Prop)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-unit; is-decidable-empty)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.injective-maps using (is-injective)
open import foundation.propositions using (type-Prop; is-prop)
open import foundation.subtypes using
  ( subtype; type-subtype; inclusion-subtype; is-emb-inclusion-subtype;
    emb-subtype; is-injective-inclusion-subtype; is-in-subtype;
    is-prop-is-in-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)
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
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where
  
  subtype-decidable-subtype : subtype l2 A
  subtype-decidable-subtype a = prop-decidable-Prop (P a)

  is-decidable-subtype-subtype-decidable-subtype :
    is-decidable-subtype subtype-decidable-subtype
  is-decidable-subtype-subtype-decidable-subtype a =
    is-decidable-type-decidable-Prop (P a)

  is-in-decidable-subtype : A → UU l2
  is-in-decidable-subtype = is-in-subtype subtype-decidable-subtype

  is-prop-is-in-decidable-subtype :
    (a : A) → is-prop (is-in-decidable-subtype a)
  is-prop-is-in-decidable-subtype =
    is-prop-is-in-subtype subtype-decidable-subtype
```

### The underlying type of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where
  
  type-decidable-subtype : UU (l1 ⊔ l2)
  type-decidable-subtype = type-subtype (subtype-decidable-subtype P)

  inclusion-decidable-subtype : type-decidable-subtype → A
  inclusion-decidable-subtype = inclusion-subtype (subtype-decidable-subtype P)

  is-emb-inclusion-decidable-subtype : is-emb inclusion-decidable-subtype
  is-emb-inclusion-decidable-subtype =
    is-emb-inclusion-subtype (subtype-decidable-subtype P)

  is-injective-inclusion-decidable-subtype :
    is-injective inclusion-decidable-subtype
  is-injective-inclusion-decidable-subtype =
    is-injective-inclusion-subtype (subtype-decidable-subtype P)

  emb-decidable-subtype : type-decidable-subtype ↪ A
  emb-decidable-subtype = emb-subtype (subtype-decidable-subtype P)
```

## Examples

### The decidable subtypes of left and right elements in a coproduct type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-is-left : (x : coprod A B) → is-decidable (is-left x)
  is-decidable-is-left (inl x) = is-decidable-unit
  is-decidable-is-left (inr x) = is-decidable-empty

  is-left-decidable-Prop : coprod A B → decidable-Prop lzero
  pr1 (is-left-decidable-Prop x) = is-left x
  pr1 (pr2 (is-left-decidable-Prop x)) = is-prop-is-left x
  pr2 (pr2 (is-left-decidable-Prop x)) = is-decidable-is-left x

  is-decidable-is-right : (x : coprod A B) → is-decidable (is-right x)
  is-decidable-is-right (inl x) = is-decidable-empty
  is-decidable-is-right (inr x) = is-decidable-unit

  is-right-decidable-Prop : coprod A B → decidable-Prop lzero
  pr1 (is-right-decidable-Prop x) = is-right x
  pr1 (pr2 (is-right-decidable-Prop x)) = is-prop-is-right x
  pr2 (pr2 (is-right-decidable-Prop x)) = is-decidable-is-right x
```
