# Iterated dependent pair types

```agda
module foundation.iterated-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.telescopes
open import foundation.universe-levels
```

</details>

## Idea

**Iterated dependent pair types** are defined by iteratively applying the
[dependent pair](foundation.dependent-pair-types.md) operator `Σ`. More
formally, `iterated-Σ` is defined as an operation `telescope l n → UU l` from
the type of [telescopes](foundation.telescopes.md) to the universe of types of
universe level `l`. For example, the iterated dependent pair type of the
telescope

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
iterated-Σ : {l : Level} {n : ℕ} → telescope l n → UU l
iterated-Σ (base-telescope A) = A
iterated-Σ (cons-telescope A) = Σ _ (λ x → iterated-Σ (A x))
```

### Iterated elements of iterated type families

```agda
data
  iterated-element : {l : Level} {n : ℕ} → telescope l n → UUω
  where
  base-iterated-element :
    {l1 : Level} {A : UU l1} → A → iterated-element (base-telescope A)
  cons-iterated-element :
    {l1 l2 : Level} {n : ℕ} {X : UU l1} {Y : X → telescope l2 n} →
    (x : X) → iterated-element (Y x) → iterated-element (cons-telescope Y)
```

### Iterated pairing

```agda
iterated-pair :
  {l : Level} {n : ℕ} {A : telescope l n} →
  iterated-element A → iterated-Σ A
iterated-pair (base-iterated-element x) = x
iterated-pair (cons-iterated-element x a) = x , iterated-pair a
```
