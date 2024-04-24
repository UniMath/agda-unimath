# Null types

```agda
module orthogonal-factorization-systems.null-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.retracts-of-maps
open import foundation.retracts-of-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-maps
open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.orthogonal-maps
```

</details>

## Idea

A type `A` is said to be
{{#concept "null at" Disambiguation="type" Agda=is-null}} `Y`, or
{{#concept "`Y`-null" Disambiguation="type" Agda=is-null}}, if the
[diagonal map](foundation.diagonal-maps-of-types.md)

```text
  Δ : A → (Y → A)
```

is an [equivalence](foundation-core.equivalences.md). The idea is that `A`
"observes" the type `Y` to be
[contractible](foundation-core.contractible-types.md).

## Definitions

### The predicate on a type of being `Y`-null

```agda
module _
  {l1 l2 : Level} (Y : UU l1) (A : UU l2)
  where

  is-null : UU (l1 ⊔ l2)
  is-null = is-equiv (diagonal-exponential A Y)

  is-prop-is-null : is-prop is-null
  is-prop-is-null = is-property-is-equiv (diagonal-exponential A Y)

  is-null-Prop : Prop (l1 ⊔ l2)
  pr1 is-null-Prop = is-null
  pr2 is-null-Prop = is-prop-is-null
```

## Properties

### `Y`-null types are closed under equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4}
  where

  is-null-equiv : (e : X ≃ Y) (f : B ≃ A) → is-null Y A → is-null X B
  is-null-equiv e f H =
    is-equiv-htpy-equiv
      ( equiv-precomp e B ∘e equiv-postcomp Y (inv-equiv f) ∘e (_ , H) ∘e f)
      ( λ b → eq-htpy (λ _ → inv (is-retraction-map-inv-equiv f b)))

  is-null-equiv-exponent : (e : X ≃ Y) → is-null Y A → is-null X A
  is-null-equiv-exponent e H =
    is-equiv-comp
      ( precomp (map-equiv e) A)
      ( diagonal-exponential A Y)
      ( H)
      ( is-equiv-precomp-equiv e A)
```

### `Y`-null types are closed under retracts

```agda
  is-null-retract : (f : B retract-of A) → is-null Y A → is-null Y B
  is-null-retract f =
    is-equiv-retract-map-is-equiv
      ( diagonal-exponential B Y)
      ( diagonal-exponential A Y)
      ( retract-map-diagonal-exponential-retract Y f)
```

### A type is `Y`-null if and only if it is local at the terminal projection `Y → unit`

```agda
module _
  {l1 l2 : Level} (Y : UU l1) (A : UU l2)
  where

  is-local-terminal-map-is-null : is-null Y A → is-local (terminal-map Y) A
  is-local-terminal-map-is-null =
    is-equiv-comp
      ( diagonal-exponential A Y)
      ( map-left-unit-law-function-type A)
      ( is-equiv-map-left-unit-law-function-type A)

  is-null-is-local-terminal-map : is-local (terminal-map Y) A → is-null Y A
  is-null-is-local-terminal-map =
    is-equiv-comp
      ( precomp (terminal-map Y) A)
      ( map-inv-left-unit-law-function-type A)
      ( is-equiv-map-inv-left-unit-law-function-type A)

  equiv-is-local-terminal-map-is-null :
    is-null Y A ≃ is-local (terminal-map Y) A
  equiv-is-local-terminal-map-is-null =
    equiv-iff-is-prop
      ( is-property-is-equiv (diagonal-exponential A Y))
      ( is-property-is-equiv (precomp (terminal-map Y) A))
      ( is-local-terminal-map-is-null)
      ( is-null-is-local-terminal-map)

  equiv-is-null-is-local-terminal-map :
    is-local (terminal-map Y) A ≃ is-null Y A
  equiv-is-null-is-local-terminal-map =
    inv-equiv equiv-is-local-terminal-map-is-null
```

### A type is `Y`-null if and only if the terminal projection of `Y` is orthogonal to the terminal projection of `A`

```agda
module _
  {l1 l2 : Level} (Y : UU l1) (A : UU l2)
  where

  is-null-is-orthogonal-terminal-maps :
    is-orthogonal (terminal-map Y) (terminal-map A) → is-null Y A
  is-null-is-orthogonal-terminal-maps H =
    is-null-is-local-terminal-map Y A
      ( is-local-is-orthogonal-terminal-map (terminal-map Y) H)
```

The converse remains to be formalized.

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
