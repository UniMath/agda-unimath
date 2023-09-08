# Local maps

```agda
module orthogonal-factorization-systems.local-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.transport
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

A map `g : A → B` is said to be **local at** `f : Y → X`, or **`f`-local**, if
all its [fibers](foundation-core.fibers-of-maps.md) are. Likewise, a family
`B : A → UU l` is local at `f` if each `B x` is.

## Definition

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-family :
    {l3 l4 : Level} {A : UU l3} → (A → UU l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-family {A = A} B = (x : A) → is-local f (B x)

  is-local-map :
    {l3 l4 : Level} {A : UU l3} {B : UU l4} → (A → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-map g = is-local-family (fiber g)
```

## Properties

### Being local is a property

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-property-is-local-family :
    {l3 l4 : Level} {A : UU l3}
    (B : A → UU l4) → is-prop (is-local-family f B)
  is-property-is-local-family B =
    is-prop-Π (λ x → is-property-is-equiv (precomp f (B x)))

  is-local-family-Prop :
    {l3 l4 : Level} {A : UU l3}
    (B : A → UU l4) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 (is-local-family-Prop B) = is-local-family f B
  pr2 (is-local-family-Prop B) = is-property-is-local-family B

  is-property-is-local-map :
    {l3 l4 : Level} {A : UU l3} {B : UU l4}
    (g : A → B) → is-prop (is-local-map f g)
  is-property-is-local-map g = is-property-is-local-family (fiber g)

  is-local-map-Prop :
    {l3 l4 : Level} {A : UU l3} {B : UU l4}
    (g : A → B) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-map-Prop g = is-local-family-Prop (fiber g)
```

### A type `B` is `f`-local if and only if the terminal projection `B → unit` is `f`-local

This remains to be formalized.

### A map is `f`-local if and only if it is `f`-orthogonal

This remains to be formalized.

## See also

- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
