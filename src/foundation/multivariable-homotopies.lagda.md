# Multivariable homotopies

```agda
module foundation.multivariable-homotopies where

open import foundation.telescopes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.iterated-dependent-product-types
open import foundation.universe-levels

open import foundation-core.functoriality-dependent-function-types
open import foundation-core.identity-types
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
multivariable-htpy {{cons-telescope {X = X} A}} f g =
  (x : X) → multivariable-htpy {{A x}} (f x) (g x)
```

### Multivariable homotopies between implicit functions

```agda
multivariable-htpy-implicit :
  {l : Level} {n : ℕ} {{A : telescope l n}} (f g : iterated-implicit-Π A) → UU l
multivariable-htpy-implicit {{base-telescope A}} f g = f ＝ g
multivariable-htpy-implicit {{cons-telescope A}} f g =
  (x : _) → multivariable-htpy-implicit {{A x}} (f {x}) (g {x})
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

equiv-eq-multivariable-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → multivariable-htpy {{A}} f g ≃ (f ＝ g)
equiv-eq-multivariable-htpy n {{A}} {f} {g} =
  inv-equiv (equiv-iterated-funext n {{A}} {f} {g})
```

### Iterated function extensionality for implicit functions

```agda
refl-multivariable-htpy-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f : iterated-implicit-Π A} →
  multivariable-htpy-implicit {{A}} f f
refl-multivariable-htpy-implicit .0 {{base-telescope A}} = refl
refl-multivariable-htpy-implicit ._ {{cons-telescope A}} x =
  refl-multivariable-htpy-implicit _ {{A x}}

multivariable-htpy-eq-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  Id {A = iterated-implicit-Π A} f g → multivariable-htpy-implicit {{A}} f g
multivariable-htpy-eq-implicit .0 {{base-telescope A}} p = p
multivariable-htpy-eq-implicit ._ {{cons-telescope A}} p x =
  multivariable-htpy-eq-implicit _ {{A x}} (htpy-eq-implicit p x)

eq-multivariable-htpy-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  multivariable-htpy-implicit {{A}} f g → Id {A = iterated-implicit-Π A} f g
eq-multivariable-htpy-implicit .0 {{base-telescope A}} H = H
eq-multivariable-htpy-implicit ._ {{cons-telescope A}} H =
  eq-htpy-implicit (λ x → eq-multivariable-htpy-implicit _ {{A x}} (H x))

equiv-iterated-funext-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  (Id {A = iterated-implicit-Π A} f g) ≃ multivariable-htpy-implicit {{A}} f g
equiv-iterated-funext-implicit .0 {{base-telescope A}} = id-equiv
equiv-iterated-funext-implicit ._ {{cons-telescope A}} =
  ( equiv-Π-equiv-family (λ x → equiv-iterated-funext-implicit _ {{A x}})) ∘e
  ( equiv-funext-implicit)
```

## See also

- [Binary homotopies](foundation.binary-homotopies.md) for once-iterated
  homotopies.
