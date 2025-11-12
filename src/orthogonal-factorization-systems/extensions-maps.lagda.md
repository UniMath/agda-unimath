# Extensions of maps

```agda
module orthogonal-factorization-systems.extensions-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-dependent-maps
```

</details>

## Idea

An
{{#concept "extension" Disambiguation="of a map along a map, types" Agda=extension-map}}
of a map `f : A → X` along a map `i : A → B` is a map `g : B → X` such that `g`
restricts along `i` to `f`.

```text
    A
    |  \
  i |    \ f
    |      \
    ∨    g   ∨
    B ------> X
```

## Definition

### Extensions of functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-extension-of-map : {X : UU l3} → (A → X) → (B → X) → UU (l1 ⊔ l3)
  is-extension-of-map = is-extension-of-dependent-map i

  extension-map :
    {X : UU l3} → (A → X) → UU (l1 ⊔ l2 ⊔ l3)
  extension-map {X} = extension-dependent-map i (λ _ → X)

  total-extension-map : (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension-map X = total-extension-dependent-map i (λ _ → X)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {i : A → B}
  {X : UU l3} {f : A → X}
  where

  map-extension-map : extension-map i f → B → X
  map-extension-map = pr1

  is-extension-map-extension-map :
    (E : extension-map i f) → is-extension-of-map i f (map-extension-map E)
  is-extension-map-extension-map = pr2
```

## Operations

#### Horizontal composition of extensions of ordinary maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  {f : A → B} {g : A → C} {h : A → X}
  {i : B → C} {j : C → X}
  where

  is-extension-of-map-comp-horizontal :
    is-extension-of-map f g i →
    is-extension-of-map g h j →
    is-extension-of-map f h (j ∘ i)
  is-extension-of-map-comp-horizontal I J x = J x ∙ ap j (I x)
```

## Properties

### The total type of extensions is equivalent to `B → X`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  inv-compute-total-extension-map :
    {X : UU l3} → total-extension-map i X ≃ (B → X)
  inv-compute-total-extension-map = inv-compute-total-extension-dependent-map i

  compute-total-extension-map :
    {X : UU l3} → (B → X) ≃ total-extension-map i X
  compute-total-extension-map = compute-total-extension-dependent-map i
```

## Examples

### The identity is an extension-map of every map along themselves

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-extension-of-map-along-self : is-extension-of-map f f id
  is-extension-of-map-along-self = refl-htpy

  self-extension-map : extension-map f f
  self-extension-map = (id , is-extension-of-map-along-self)
```

## See also

- [`orthogonal-factorization-systems.lifts-maps`](orthogonal-factorization-systems.lifts-maps.md)
  for the dual notion.
