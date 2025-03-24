# Families of equivalences

```agda
open import foundation.function-extensionality-axiom

module foundation.families-of-equivalences
  (funext : function-extensionality)
  where

open import foundation-core.families-of-equivalences public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

A **family of equivalences** is a family

```text
  eᵢ : A i ≃ B i
```

of [equivalences](foundation-core.equivalences.md). Families of equivalences are
also called **fiberwise equivalences**.

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

## See also

- In
  [Functoriality of dependent pair types](foundation-core.functoriality-dependent-pair-types.md)
  we show that a family of maps is a fiberwise equivalence if and only if it
  induces an equivalence on [total spaces](foundation.dependent-pair-types.md).
