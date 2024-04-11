# Null types

```agda
module orthogonal-factorization-systems.null-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.logical-equivalences
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

A type `A` is said to be **null at** `Y`, or **`Y`-null**, if the constant map

```text
  const : A → (Y → A)
```

is an equivalence. The idea is that _`A` observes the type `Y` to be
contractible_.

## Definition

```agda
module _
  {l1 l2 : Level} (Y : UU l1) (A : UU l2)
  where

  is-null : UU (l1 ⊔ l2)
  is-null = is-equiv (const Y A)

  is-prop-is-null : is-prop is-null
  is-prop-is-null = is-property-is-equiv (const Y A)

  is-null-Prop : Prop (l1 ⊔ l2)
  pr1 is-null-Prop = is-null
  pr2 is-null-Prop = is-prop-is-null
```

## Properties

### A type is `Y`-null if and only if it is local at the terminal projection `Y → unit`

```agda
module _
  {l1 l2 : Level} (Y : UU l1) (A : UU l2)
  where

  is-local-is-null : is-null Y A → is-local (λ y → star) A
  is-local-is-null =
    is-equiv-comp
      ( const Y A)
      ( map-left-unit-law-function-type A)
      ( is-equiv-map-left-unit-law-function-type A)

  is-null-is-local : is-local (λ y → star) A → is-null Y A
  is-null-is-local =
    is-equiv-comp
      ( precomp (λ y → star) A)
      ( map-inv-left-unit-law-function-type A)
      ( is-equiv-map-inv-left-unit-law-function-type A)

  equiv-is-local-is-null : is-null Y A ≃ is-local (λ y → star) A
  equiv-is-local-is-null =
    equiv-iff-is-prop
      ( is-property-is-equiv (const Y A))
      ( is-property-is-equiv (precomp (λ y → star) A))
      ( is-local-is-null)
      ( is-null-is-local)

  equiv-is-null-is-local : is-local (λ y → star) A ≃ is-null Y A
  equiv-is-null-is-local = inv-equiv equiv-is-local-is-null
```

### A type is `f`-local if it is null at every fiber of `f`

```agda
module _
  {l1 l2 l3 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type-is-null-fiber :
    (A : X → UU l3) →
    ((x : X) → is-null (fiber f x) (A x)) → is-local-dependent-type f A
  is-local-dependent-type-is-null-fiber A = is-equiv-precomp-Π-fiber-condition

  is-local-is-null-fiber :
    (A : UU l3) → ((x : X) → is-null (fiber f x) A) → is-local f A
  is-local-is-null-fiber A = is-local-dependent-type-is-null-fiber (λ _ → A)
```
