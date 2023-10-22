# Multivariable homotopies

```agda
module foundation.multivariable-homotopies where

open import foundation.telescopes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-extensionality
open import foundation.iterated-dependent-product-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

Given an
[iterated dependent product](foundation.iterated-dependent-product-types.md) we
can consider [homotopies](foundation-core.homotopies.md) of its elements. By
[function extensionality](foundation.function-extensionality.md),
**multivariable homotopies** are [equivalent](foundation-core.equivalences.md)
to [identifications](foundation-core.identity-types.md).

## Definitions

### Multivariable homotopies

```agda
multivariable-htpy :
  {l : Level} {n : ℕ} {{A : telescope l n}} (f g : iterated-Π A) → UU l
multivariable-htpy {{base-telescope A}} f g = f ＝ g
multivariable-htpy {{cons-telescope A}} f g =
  (x : _) → multivariable-htpy {{A x}} (f x) (g x)
```

### Iterated function extensionality

```agda
refl-multivariable-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f : iterated-Π A} → multivariable-htpy {{A}} f f
refl-multivariable-htpy .0 {{base-telescope A}} = refl
refl-multivariable-htpy ._ {{cons-telescope A}} x =
  refl-multivariable-htpy _ {{A x}}

multivariable-htpy-eq :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → f ＝ g → multivariable-htpy {{A}} f g
multivariable-htpy-eq .0 {{base-telescope A}} p = p
multivariable-htpy-eq ._ {{cons-telescope A}} p x =
  multivariable-htpy-eq _ {{A x}} (htpy-eq p x)

eq-multivariable-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → multivariable-htpy {{A}} f g → f ＝ g
eq-multivariable-htpy .0 {{base-telescope A}} H = H
eq-multivariable-htpy ._ {{cons-telescope A}} H =
  eq-htpy (λ x → eq-multivariable-htpy _ {{A x}} (H x))

equiv-iterated-funext :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → (f ＝ g) ≃ multivariable-htpy {{A}} f g
equiv-iterated-funext .0 {{base-telescope A}} = id-equiv
equiv-iterated-funext ._ {{cons-telescope A}} =
  equiv-Π-equiv-family (λ x → equiv-iterated-funext _ {{A x}}) ∘e equiv-funext
```

## See also

- [Binary homotopies](foundation.binary-homotopies.md) for once-iterated
  homotopies.
