# Iterated dependent product types

```agda
module foundation.iterated-dependent-product-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.iterated-type-families
open import foundation.universe-levels
```

</details>

## Idea

Given an [iterated family of types](foundation.iterated-type-families.md) `A`,
the **iterated dependent product** of `A` is defined by iteratively taking the
dependent product of the types in `A`. For example, the iterated dependent
product of the iterated type family

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
  {l : Level} {n : ℕ} → iterated-type-family l n → UU l
iterated-Π (base-iterated-type-family A) =
  A
iterated-Π (cons-iterated-type-family A) =
  (x : _) → iterated-Π (A x)
```
