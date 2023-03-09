# Involutions

```agda
module foundation-core.involutions where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.automorphisms
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

An involution on a type `A` is a map (or an equivalence) `f : A → A` such that `(f ∘ f) ~ id`

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  is-involution : (A → A) → UU l
  is-involution f = (f ∘ f) ~ id

  is-involution-aut : Aut A → UU l
  is-involution-aut e = is-involution (map-equiv e)
```

### The type of involutions on `A`

```agda
involution : {l : Level} → UU l → UU l
involution A = Σ (A → A) is-involution

module _
  {l : Level} {A : UU l} (f : involution A)
  where

  map-involution : A → A
  map-involution = pr1 f

  is-involution-map-involution : is-involution map-involution
  is-involution-map-involution = pr2 f
```

## Properties

### Any involution is an equivalence

```agda
is-equiv-is-involution :
  {l : Level} {A : UU l} {f : A → A} → is-involution f → is-equiv f
is-equiv-is-involution {f = f} is-involution-f =
  is-equiv-has-inverse f is-involution-f is-involution-f

equiv-is-involution :
  {l : Level} {A : UU l} {f : A → A} → is-involution f → A ≃ A
pr1 (equiv-is-involution {f = f} is-involution-f) = f
pr2 (equiv-is-involution is-involution-f) =
  is-equiv-is-involution is-involution-f
```

### If `A` is k-truncated then the type of involutions is k-truncated

```agda
is-trunc-is-involution :
  {l : Level} {A : UU l} (k : 𝕋) →
  is-trunc (succ-𝕋 k) A → (f : A → A) → is-trunc k (is-involution f)
is-trunc-is-involution k is-trunc-A f = is-trunc-Π k λ x → is-trunc-A (f(f x)) x

is-involution-Truncated-Type : {l : Level} {A : UU l} (k : 𝕋) →
  is-trunc (succ-𝕋 k) A → (A → A) → Truncated-Type l k
pr1 (is-involution-Truncated-Type k is-trunc-A f) = is-involution f
pr2 (is-involution-Truncated-Type k is-trunc-A f) =
  is-trunc-is-involution k is-trunc-A f

is-trunc-involution :
  {l : Level} {A : UU l} (k : 𝕋) →
  is-trunc k A → is-trunc k (involution A)
is-trunc-involution k is-trunc-A =
  is-trunc-Σ
    (is-trunc-function-type k is-trunc-A)
    (is-trunc-is-involution k (is-trunc-succ-is-trunc k is-trunc-A))

involution-Truncated-Type :
  {l : Level} {k : 𝕋} → Truncated-Type l k → Truncated-Type l k
involution-Truncated-Type {k = k} (A , is-trunc-A) =
  involution A , is-trunc-involution k is-trunc-A
```

### The identity function is an involution

```agda
is-involution-id :
  {l : Level} {A : UU l} → is-involution (id {A = A})
is-involution-id = refl-htpy

id-involution :
  {l : Level} {A : UU l} → involution A
pr1 id-involution = id
pr2 id-involution = is-involution-id

involution-Pointed-Type :
  {l : Level} (A : UU l) → Pointed-Type l
pr1 (involution-Pointed-Type A) = involution A
pr2 (involution-Pointed-Type A) = id-involution
```
