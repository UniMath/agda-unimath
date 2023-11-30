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
open import foundation.equality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.dependent-pair-types
open import foundation.torsorial-type-families
open import foundation.iterated-dependent-product-types
open import foundation.universe-levels

open import foundation-core.functoriality-dependent-function-types
open import foundation-core.contractible-types
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
multivariable-implicit-htpy :
  {l : Level} {n : ℕ} {{A : telescope l n}} (f g : iterated-implicit-Π A) → UU l
multivariable-implicit-htpy {{base-telescope A}} f g = f ＝ g
multivariable-implicit-htpy {{cons-telescope {X = X} A}} f g =
  (x : X) → multivariable-implicit-htpy {{A x}} (f {x}) (g {x})
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
refl-multivariable-implicit-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f : iterated-implicit-Π A} →
  multivariable-implicit-htpy {{A}} f f
refl-multivariable-implicit-htpy .0 {{base-telescope A}} = refl
refl-multivariable-implicit-htpy ._ {{cons-telescope A}} x =
  refl-multivariable-implicit-htpy _ {{A x}}

multivariable-htpy-eq-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  Id {A = iterated-implicit-Π A} f g → multivariable-implicit-htpy {{A}} f g
multivariable-htpy-eq-implicit .0 {{base-telescope A}} p = p
multivariable-htpy-eq-implicit ._ {{cons-telescope A}} p x =
  multivariable-htpy-eq-implicit _ {{A x}} (htpy-eq-implicit p x)

eq-multivariable-implicit-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  multivariable-implicit-htpy {{A}} f g → Id {A = iterated-implicit-Π A} f g
eq-multivariable-implicit-htpy .0 {{base-telescope A}} H = H
eq-multivariable-implicit-htpy ._ {{cons-telescope A}} H =
  eq-implicit-htpy (λ x → eq-multivariable-implicit-htpy _ {{A x}} (H x))

equiv-iterated-funext-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  (Id {A = iterated-implicit-Π A} f g) ≃ multivariable-implicit-htpy {{A}} f g
equiv-iterated-funext-implicit .0 {{base-telescope A}} = id-equiv
equiv-iterated-funext-implicit ._ {{cons-telescope A}} =
  ( equiv-Π-equiv-family (λ x → equiv-iterated-funext-implicit _ {{A x}})) ∘e
  ( equiv-funext-implicit)
```

### Torsoriality of multivariable homotopies

```agda
is-torsorial-multivariable-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}} (f : iterated-Π A) →
  is-torsorial (multivariable-htpy {{A}} f)
is-torsorial-multivariable-htpy ._ {{base-telescope A}} = is-torsorial-path
is-torsorial-multivariable-htpy ._ {{cons-telescope A}} f =
  is-torsorial-Eq-Π
    ( λ x → multivariable-htpy {{A x}} (f x))
    ( λ x → is-torsorial-multivariable-htpy _ {{A x}} (f x))

is-torsorial-multivariable-implicit-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}} (f : iterated-implicit-Π A) →
  is-torsorial (multivariable-implicit-htpy {{A}} f)
is-torsorial-multivariable-implicit-htpy ._ {{A}} f =
  is-contr-equiv'
    ( Σ (iterated-implicit-Π (A)) (Id {A = iterated-implicit-Π A} f))
    ( equiv-tot (λ x → equiv-iterated-funext-implicit _ {{A}}))
    ( is-torsorial-path {A = iterated-implicit-Π A} f)
```

## See also

- [Binary homotopies](foundation.binary-homotopies.md) for once-iterated
  homotopies.
