# Iterated dependent product types

```agda
module foundation.iterated-dependent-product-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.telescopes
open import foundation.universe-levels
```

</details>

## Idea

**Iterated dependent products** are defined by iteratively applying the built in
dependent function type operator. More formally, `iterated-Π` is defined as an
operation `telescope l n → UU l` from the type of
[telescopes](foundation.telescopes.md) to the universe of types of universe
level `l`. For example, the iterated dependent product of the telescope

```text
  A₀ : 𝒰 l₀
  A₁ : A₀ → 𝒰 l₁
  A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰 l₂
  A₃ : (x₀ : A₀) (x₁ : A₁ x₀) → A₂ x₀ x₁ → 𝒰 l₃
```

is the dependent product type

```text
  (x₀ : A₀) (x₁ : A₁ x₀) (x₂ : A₂ x₀ x₁) → A₃ x₀ x₁ x₂
```

of universe level `l₀ ⊔ l₁ ⊔ l₂ ⊔ l₃`.

## Definitions

### Iterated dependent products of iterated type families

```agda
iterated-Π :
  {l : Level} {n : ℕ} → telescope l n → UU l
iterated-Π (base-telescope A) = A
iterated-Π (cons-telescope A) = (x : _) → iterated-Π (A x)
```

### Iterated sections of type families

```agda
data
  iterated-section : {l : Level} {n : ℕ} → telescope l n → UUω
  where
  base-iterated-section :
    {l1 : Level} {A : UU l1} → A → iterated-section (base-telescope A)
  cons-iterated-section :
    {l1 l2 : Level} {n : ℕ} {X : UU l1} {Y : X → telescope l2 n} →
    ((x : X) → iterated-section (Y x)) → iterated-section (cons-telescope Y)
```

### Iterated λ-abstractions

```agda
iterated-λ :
  {l : Level} {n : ℕ} {A : telescope l n} →
  iterated-section A → iterated-Π A
iterated-λ (base-iterated-section a) = a
iterated-λ (cons-iterated-section f) x = iterated-λ (f x)
```

### Transforming iterated products

Given an operation on universes, we can apply it at the base of the iterated
product.

```agda
apply-base-iterated-Π :
  {l1 : Level} {n : ℕ}
  (P : {l : Level} → UU l → UU l) → telescope l1 n → UU l1
apply-base-iterated-Π P (base-telescope A) = P A
apply-base-iterated-Π P (cons-telescope A) =
  (x : _) → apply-base-iterated-Π P (A x)
```
