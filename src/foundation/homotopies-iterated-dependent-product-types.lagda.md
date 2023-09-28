# Homotopies in iterated dependent product types

```agda
module foundation.homotopies-iterated-dependent-product-types where

open import foundation.telescopes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
open import foundation.iterated-dependent-product-types
open import foundation.function-extensionality

open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.identity-types
open import foundation-core.contractible-types
open import foundation-core.propositions
```

</details>

## Idea

Given an
[iterated dependent product](foundation.iterated-dependent-product-types.md) we
can consider [homotopies](foundation-core.homotopies.md) of its elements.

## Definitions

### Homotopies in iterated dependent products of iterated type families

```agda
htpy-iterated-Π :
  {l : Level} {n : ℕ} {{A : telescope l n}} → (f g : iterated-Π A) → UU l
htpy-iterated-Π {{base-telescope A}} f g = f ＝ g
htpy-iterated-Π {{cons-telescope A}} f g =
  (x : _) → htpy-iterated-Π {{A x}} (f x) (g x)
```

### Iterated function extensionality

```agda
iterated-eq-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → htpy-iterated-Π {{A}} f g → f ＝ g
iterated-eq-htpy .0 {{ base-telescope A}} H = H
iterated-eq-htpy ._ {{cons-telescope A}} H =
  eq-htpy (λ x → iterated-eq-htpy _ {{A x}} (H x))
```
