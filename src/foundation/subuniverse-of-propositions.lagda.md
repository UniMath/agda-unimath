# The subuniverse of propositions

```agda
module foundation.subuniverse-of-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.logical-equivalences
open import foundation.subuniverse-of-contractible-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Idea

We show that being a [proposition](foundation-core.propositions.md) is a
property, and thus we obtain a [subuniverse](foundation.subuniverses.md) of
propositions.

## Definition

### Being a proposition is a property

```agda
abstract
  is-property-is-prop :
    {l : Level} (A : UU l) → is-prop (is-prop A)
  is-property-is-prop A =
    is-prop-Π (λ x → is-prop-Π (λ y → is-property-is-contr))

is-prop-Prop : {l : Level} (A : UU l) → Prop l
pr1 (is-prop-Prop A) = is-prop A
pr2 (is-prop-Prop A) = is-property-is-prop A
```

## Properties

### Two equivalent types are equivalently propositions

```agda
equiv-is-prop-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-prop A ≃ is-prop B
equiv-is-prop-equiv {A = A} {B = B} e =
  equiv-iff-is-prop
    ( is-property-is-prop A)
    ( is-property-is-prop B)
    ( is-prop-equiv' e)
    ( is-prop-equiv e)
```

## See also

- The characterization of the identity type of the subuniverse of propositions
  is [propositional extensionality](foundation.propositional-extensionality.md).
