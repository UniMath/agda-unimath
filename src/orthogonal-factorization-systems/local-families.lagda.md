# Local families

```agda
module orthogonal-factorization-systems.local-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

A family `B : A → UU l` is said to be **local at** `f : Y → X`, or
**`f`-local**, if every [fiber](foundation-core.fibers-of-maps.md) is.

## Definition

```agda
is-local-family :
  {l1 l2 l3 l4 : Level} {Y : UU l1} {X : UU l2}
  (f : Y → X) {A : UU l3} → (A → UU l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-local-family f {A} B = (x : A) → is-local f (B x)
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
```

### A family is `f`-local if and only if it is `f`-orthogonal

This remains to be formalized.

## See also

- [Local maps](orthogonal-factorization-systems.local-maps.md)
- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
