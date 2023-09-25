# Iterated dependent pair types

```agda
module foundation.iterated-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.iterated-type-families
open import foundation.universe-levels
```

</details>

## Idea

Given an [iterated family of types](foundation.iterated-type-families.md) `A`,
the **iterated dependent pair types** of `A` is defined by iteratively taking
the [dependent pair type](foundation.dependent-pair-types.md) of the types in
`A`. For example, the iterated dependent pair type of the iterated type family

```text
  A₀ : 𝒰 l₀
  A₁ : A₀ → 𝒰 l₁
  A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰 l₂
  A₃ : (x₀ : A₀) (x₁ : A₁ x₀) → A₂ x₀ x₁ → 𝒰 l₃
```

is the dependent pair type

```text
  Σ A₀ (λ x₀ → Σ (A₁ x₀) (λ x₁ → Σ (A₂ x₀ x₁) (A₃ x₀ x₁)))
```

of universe level `l₀ ⊔ l₁ ⊔ l₂ ⊔ l₃`.

## Definitions

### Iterated dependent products of iterated type families

```agda
iterated-Σ :
  {l : Level} {n : ℕ} → iterated-type-family l n → UU l
iterated-Σ (base-iterated-type-family A) =
  A
iterated-Σ (cons-iterated-type-family A) =
  Σ _ (λ x → iterated-Σ (A x))
```
