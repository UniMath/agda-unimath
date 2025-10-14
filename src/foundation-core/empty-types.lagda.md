# Empty types

```agda
module foundation-core.empty-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

An **empty type** is a type with no elements. The (standard) empty type is
introduced as an inductive type with no constructors. With the standard empty
type available, we will say that a type is empty if it maps into the standard
empty type.

## Definition

### Empty types

```agda
data empty : UU lzero where

ind-empty : {l : Level} {P : empty → UU l} → ((x : empty) → P x)
ind-empty ()

ex-falso : {l : Level} {A : UU l} → empty → A
ex-falso = ind-empty

is-empty : {l : Level} → UU l → UU l
is-empty A = A → empty

is-nonempty : {l : Level} → UU l → UU l
is-nonempty A = is-empty (is-empty A)
```

## Properties

### The map `ex-falso` is an embedding

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-emb-ex-falso : is-emb (ex-falso {A = A})
    is-emb-ex-falso ()

  ex-falso-emb : empty ↪ A
  pr1 ex-falso-emb = ex-falso
  pr2 ex-falso-emb = is-emb-ex-falso
```

### Any map into an empty type is an equivalence

```agda
abstract
  is-equiv-is-empty :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-empty B → is-equiv f
  is-equiv-is-empty f H =
    is-equiv-is-invertible
      ( ex-falso ∘ H)
      ( λ y → ex-falso (H y))
      ( λ x → ex-falso (H (f x)))

abstract
  is-equiv-is-empty' :
    {l : Level} {A : UU l} (f : is-empty A) → is-equiv f
  is-equiv-is-empty' f = is-equiv-is-empty f id

equiv-is-empty' : {l : Level} {A : UU l} → is-empty A → A ≃ empty
equiv-is-empty' f = (f , is-equiv-is-empty' f)

equiv-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty A → is-empty B → A ≃ B
equiv-is-empty f g =
  ( inv-equiv (pair g (is-equiv-is-empty g id))) ∘e
  ( pair f (is-equiv-is-empty f id))
```

### Any map into an empty type is an embedding

```agda
abstract
  is-emb-is-empty :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-empty B → is-emb f
  is-emb-is-empty f H = is-emb-is-equiv (is-equiv-is-empty f H)
```

### The empty type is a proposition

```agda
abstract
  is-prop-empty : is-prop empty
  is-prop-empty ()

empty-Prop : Prop lzero
pr1 empty-Prop = empty
pr2 empty-Prop = is-prop-empty

is-prop-is-empty : {l : Level} {A : UU l} → is-empty A → is-prop A
is-prop-is-empty is-empty-A = ex-falso ∘ is-empty-A
```

### The empty type is a set

```agda
is-set-empty : is-set empty
is-set-empty ()

empty-Set : Set lzero
pr1 empty-Set = empty
pr2 empty-Set = is-set-empty
```

### The empty type is `k`-truncated for any `k ≥ 1`

```agda
abstract
  is-trunc-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
  is-trunc-empty k ()

empty-Truncated-Type : (k : 𝕋) → Truncated-Type lzero (succ-𝕋 k)
pr1 (empty-Truncated-Type k) = empty
pr2 (empty-Truncated-Type k) = is-trunc-empty k

abstract
  is-trunc-is-empty :
    {l : Level} (k : 𝕋) {A : UU l} → is-empty A → is-trunc (succ-𝕋 k) A
  is-trunc-is-empty k f x = ex-falso (f x)
```
