# Dependent telescopes

```agda
module foundation.dependent-telescopes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.multiplication-natural-numbers

open import foundation.dependent-pair-types
open import foundation.telescopes
open import foundation.universe-levels
```

</details>

## Idea

A **dependent telescope** over a [telescope](foundation.telescopes.md) `A` of
length `n` is a dependent list of dependent types over each of the entries in
`A`. For example, a dependent telescope over the telescope

```text
  A₀ : 𝒰 l₀
  A₁ : A₀ → 𝒰 l₁
  A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰 l₂
```

consists of

```text
  B₀ : A₀ → 𝒰 k₀
  B₁ : (x₀ : A₀) (x₁ : A₁ x₀) → B₀ x₀ → UU k₁
  B₂ : (x₀ : A₀) (x₁ : A₁ x₀) (x₂ : A₂ x₀ x₁) (y₀ : B x₀) → B₁ x₀ → UU k₂
```

## Definitions

### Dependent telescopes

```agda
data
  dependent-telescope :
    {l : Level} (k : Level) → {n : ℕ} → telescope l n → UUω
  where
  base-dependent-telescope :
    {l1 k1 : Level} {A : UU l1} → (A → UU k1) →
    dependent-telescope k1 (base-telescope A)
  cons-dependent-telescope :
    {l1 l2 k1 k2 : Level} {n : ℕ} {X : UU l1} {A : X → telescope l2 n}
    {Y : X → UU k1} (B : (x : X) → Y x → dependent-telescope k2 (A x)) →
    dependent-telescope (k1 ⊔ k2) (cons-telescope A)
```

### Expansion of telescopes

An **expansion** of a telescope `A` by a dependent telescope `B` over it is a
new telescope of the same depth as `A`, by taking dependent pairs componentwise.

```agda
expand-telescope :
  {l1 l2 : Level} {n : ℕ} {A : telescope l1 n} →
  dependent-telescope l2 A → telescope (l1 ⊔ l2) n
expand-telescope (base-dependent-telescope Y) =
  base-telescope (Σ _ Y)
expand-telescope (cons-dependent-telescope B) =
  cons-telescope (λ x → expand-telescope (B (pr1 x) (pr2 x)))
```

```agda
interleave-ℕ : ℕ → ℕ
interleave-ℕ zero-ℕ = 1
interleave-ℕ (succ-ℕ n) = succ-ℕ (succ-ℕ (interleave-ℕ n))

interleave-telescope :
  {l1 l2 : Level} {n : ℕ} {A : telescope l1 n} →
  dependent-telescope l2 A → telescope (l1 ⊔ l2) (interleave-ℕ n)
interleave-telescope (base-dependent-telescope A) =
  cons-telescope (λ x → base-telescope (A x))
interleave-telescope (cons-dependent-telescope B) =
  cons-telescope (λ x → cons-telescope λ y → interleave-telescope (B x y))
```

```agda
telescope-Π :
  {l1 l2 : Level} {n : ℕ} {A : telescope l1 n} →
  dependent-telescope l2 A → telescope (l1 ⊔ l2) n
telescope-Π (base-dependent-telescope Y) =
  base-telescope ((x : _) → Y x)
telescope-Π (cons-dependent-telescope B) =
  cons-telescope (λ x → telescope-Π (B (pr1 x) (pr2 x)))
```
