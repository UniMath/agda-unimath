# Null types

```agda
module orthogonal-factorization-systems.null-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
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
    equiv-prop
      ( is-property-is-equiv (const Y A))
      ( is-property-is-equiv (precomp (λ y → star) A))
      ( is-local-is-null)
      ( is-null-is-local)

  equiv-is-null-is-local : is-local (λ y → star) A ≃ is-null Y A
  equiv-is-null-is-local = inv-equiv equiv-is-local-is-null
```
