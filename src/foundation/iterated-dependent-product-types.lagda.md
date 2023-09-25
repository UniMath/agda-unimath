# Iterated dependent product types

```agda
module foundation.iterated-dependent-product-types where

open import foundation.telescopes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.propositions
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

Given an operation on universes, we can apply it at the codomain of the iterated
product.

```agda
apply-codomain-iterated-Π :
  {l1 : Level} {n : ℕ}
  (P : {l : Level} → UU l → UU l) → telescope l1 n → UU l1
apply-codomain-iterated-Π P A = iterated-Π (apply-base-telescope P A)
```

## Properties

### Iterated products of contractible types is contractible

```agda
is-contr-iterated-Π :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  apply-codomain-iterated-Π is-contr A → is-contr (iterated-Π A)
is-contr-iterated-Π ._ {{base-telescope A}} H = H
is-contr-iterated-Π ._ {{cons-telescope A}} H =
  is-contr-Π (λ x → is-contr-iterated-Π _ {{A x}} (H x))
```

### Iterated products of propositions are propositions

```agda
is-prop-iterated-Π :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  apply-codomain-iterated-Π is-prop A → is-prop (iterated-Π A)
is-prop-iterated-Π ._ {{base-telescope A}} H = H
is-prop-iterated-Π ._ {{cons-telescope A}} H =
  is-prop-Π (λ x → is-prop-iterated-Π _ {{A x}} (H x))
```
