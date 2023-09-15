# Homotopy induction

```agda
module foundation.homotopy-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-systems
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

The principle of **homotopy induction** asserts that homotopies form an
[identity system](foundation.identity-systems.md) on dependent function types.

## Statement

```agda
ev-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → f ~ g → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f refl-htpy
ev-refl-htpy f C φ = φ f refl-htpy

induction-principle-homotopies :
  {l1 l2 : Level} (l3 : Level) {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU (l1 ⊔ l2 ⊔ lsuc l3)
induction-principle-homotopies l3 f =
  is-identity-system l3 (f ~_) f (refl-htpy)
```

## Propositions

### The total space of homotopies is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where

  abstract
    is-contr-total-htpy : is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
    is-contr-total-htpy =
      is-contr-equiv'
        ( Σ ((x : A) → B x) (Id f))
        ( equiv-tot (λ g → equiv-funext))
        ( is-contr-total-path f)

  abstract
    is-contr-total-htpy' : is-contr (Σ ((x : A) → B x) (λ g → g ~ f))
    is-contr-total-htpy' =
      is-contr-equiv'
        ( Σ ((x : A) → B x) (λ g → g ＝ f))
        ( equiv-tot (λ g → equiv-funext))
        ( is-contr-total-path' f)
```

### Homotopy induction is equivalent to function extensionality

```agda
abstract
  induction-principle-homotopies-function-extensionality :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    function-extensionality f →
    (l3 : Level) → induction-principle-homotopies l3 f
  induction-principle-homotopies-function-extensionality
    {A = A} {B} f funext-f l3 =
    is-identity-system-is-torsorial f
      ( refl-htpy)
      ( is-contr-total-htpy f)

abstract
  function-extensionality-induction-principle-homotopies :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    ({l3 : Level} → induction-principle-homotopies l3 f) →
    function-extensionality f
  function-extensionality-induction-principle-homotopies f ind-htpy-f =
    fundamental-theorem-id-is-identity-system f
      ( refl-htpy)
      ( ind-htpy-f)
      ( λ _ → htpy-eq)
```

### Homotopy induction

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    induction-principle-htpy :
      (f : (x : A) → B x) → induction-principle-homotopies l3 f
    induction-principle-htpy f =
      induction-principle-homotopies-function-extensionality f (funext f) l3

    ind-htpy :
      (f : (x : A) → B x) (C : (g : (x : A) → B x) → f ~ g → UU l3) →
      C f refl-htpy → {g : (x : A) → B x} (H : f ~ g) → C g H
    ind-htpy f C t {g} = pr1 (induction-principle-htpy f C) t g

    compute-ind-htpy :
      (f : (x : A) → B x) (C : (g : (x : A) → B x) → f ~ g → UU l3) →
      (c : C f refl-htpy) → ind-htpy f C c refl-htpy ＝ c
    compute-ind-htpy f C = pr2 (induction-principle-htpy f C)
```

## See also

- [Homotopies](foundation.homotopies.md).
- [Function extensionality](foundation-core.function-extensionality.md).
