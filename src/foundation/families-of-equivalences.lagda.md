# Families of equivalences

```agda
module foundation.families-of-equivalences where

open import foundation-core.families-of-equivalences public
```

<details><summary>Imports</summary>

```agda
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **family of equivalences** is a family

```text
  eᵢ : A i ≃ B i
```

of [equivalences](foundation-core.equivalences.md). Families of equivalences are
also called **fiberwise equivalences**.

## Definitions

### The family of identity equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  id-fam-equiv : fam-equiv B B
  id-fam-equiv a = id-equiv
```

## Properties

### Being a fiberwise equivalence is a proposition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-property-is-fiberwise-equiv :
    (f : (a : A) → B a → C a) → is-prop (is-fiberwise-equiv f)
  is-property-is-fiberwise-equiv f =
    is-prop-Π (λ a → is-property-is-equiv (f a))
```

### TODO

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-torsorial-fam-equiv : is-torsorial (fam-equiv B)
  is-torsorial-fam-equiv =
    is-torsorial-Eq-Π (λ a → is-torsorial-equiv (B a))

  is-torsorial-fam-equiv' : is-torsorial (λ C → fam-equiv C B)
  is-torsorial-fam-equiv' =
    is-torsorial-Eq-Π (λ a → is-torsorial-equiv' (B a))
```

## See also

- In
  [Functoriality of dependent pair types](foundation-core.functoriality-dependent-pair-types.md)
  we show that a family of maps is a fiberwise equivalence if and only if it
  induces an equivalence on [total spaces](foundation.dependent-pair-types.md).
