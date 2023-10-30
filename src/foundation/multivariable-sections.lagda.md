# Multivariable sections

```agda
module foundation.multivariable-sections where

open import foundation.telescopes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.iterated-dependent-product-types
open import foundation.multivariable-homotopies
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **multivariable section** is a map of multivariable maps that is a right
inverse. Thus, a map

```text
  s : ((x₁ : A₁) ... (xₙ : Aₙ) → A x) → (y₁ : B₁) ... (yₙ : Bₙ) → B y
```

is a section of a map of type

```text
  f : ((y₁ : B₁) ... (yₙ : Bₙ) → B y) → (x₁ : A₁) ... (xₙ : Aₙ) → A x
```

if the composition `f ∘ s` is
[multivariable homotopic](foundation.multivariable-homotopies.md) to the
identity at

```text
  (y₁ : B₁) ... (yₙ : Bₙ) → B y.
```

Note that sections of multivariable maps are equivalent to common
[sections](foundation-core.sections.md) by function extensionality, so this
definition only finds it utility in avoiding unnecessary applications of
[function extensionality](foundation.function-extensionality.md). For instance,
this is useful when defining induction principles on function types.

## Definition

```agda
module _
  {l1 l2 : Level} (n : ℕ)
  {{A : telescope l1 n}} {{B : telescope l2 n}}
  (f : iterated-Π A → iterated-Π B)
  where

  multivariable-section : UU (l1 ⊔ l2)
  multivariable-section =
    Σ ( iterated-Π B → iterated-Π A)
      ( λ s →
        multivariable-htpy
          { n = succ-ℕ n}
          {{A = prepend-telescope (iterated-Π B) B}}
          ( f ∘ s)
          ( id))

  map-multivariable-section :
    multivariable-section → iterated-Π B → iterated-Π A
  map-multivariable-section = pr1

  is-multivariable-section-map-multivariable-section :
    (s : multivariable-section) →
    multivariable-htpy
      { n = succ-ℕ n}
      {{A = prepend-telescope (iterated-Π B) B}}
      ( f ∘ map-multivariable-section s)
      ( id)
  is-multivariable-section-map-multivariable-section = pr2
```
