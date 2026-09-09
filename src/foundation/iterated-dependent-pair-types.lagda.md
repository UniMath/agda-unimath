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

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
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
iterated-Σ (cons-telescope {X = X} A) = Σ X (λ x → iterated-Σ (A x))
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
pr1 (iterated-pair (cons-iterated-element y a)) = y
pr2 (iterated-pair (cons-iterated-element y a)) = iterated-pair a
```

## Properties

### Contractiblity of iterated Σ-types

```agda
is-contr-Σ-telescope : {l : Level} {n : ℕ} → telescope l n → UU l
is-contr-Σ-telescope (base-telescope A) = is-contr A
is-contr-Σ-telescope (cons-telescope {X = X} A) =
  (is-contr X) × (Σ X (λ x → is-contr-Σ-telescope (A x)))

is-contr-iterated-Σ :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  is-contr-Σ-telescope A → is-contr (iterated-Σ A)
is-contr-iterated-Σ .0 {{base-telescope A}} is-contr-A = is-contr-A
is-contr-iterated-Σ ._ {{cons-telescope A}} (is-contr-X , x , H) =
  is-contr-Σ is-contr-X x (is-contr-iterated-Σ _ {{A x}} H)
```

### Contractiblity of iterated Σ-types without choice of contracting center

```agda
is-contr-Σ-telescope' : {l : Level} {n : ℕ} → telescope l n → UU l
is-contr-Σ-telescope' (base-telescope A) = is-contr A
is-contr-Σ-telescope' (cons-telescope {X = X} A) =
  (is-contr X) × ((x : X) → is-contr-Σ-telescope' (A x))

is-contr-iterated-Σ' :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  is-contr-Σ-telescope' A → is-contr (iterated-Σ A)
is-contr-iterated-Σ' .0 {{base-telescope A}} is-contr-A = is-contr-A
is-contr-iterated-Σ' ._ {{cons-telescope A}} (is-contr-X , H) =
  is-contr-Σ' is-contr-X (λ x → is-contr-iterated-Σ' _ {{A x}} (H x))
```

## See also

- [Iterated Π-types](foundation.iterated-dependent-product-types.md)
