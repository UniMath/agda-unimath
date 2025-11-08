# Extensions of maps

```agda
module orthogonal-factorization-systems.extensions-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.monomorphisms
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.torsorial-type-families

open import orthogonal-factorization-systems.extensions-dependent-maps
```

</details>

## Idea

An **extension** of a map `f : (x : A) → P x` along a map `i : A → B` is a map
`g : (y : B) → Q y` such that `Q` restricts along `i` to `P` and `g` restricts
along `i` to `f`.

```text
  A
  |  \
  i    f
  |      \
  ∨       ∨
  B - g -> P
```

## Definition

### Extensions of dependent functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  extension :
    {X : UU l3} → (A → X) → UU (l1 ⊔ l2 ⊔ l3)
  extension {X} = extension-dependent-type i (λ _ → X)

  total-extension : (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension X = total-extension-dependent-type i (λ _ → X)
```

## Operations

#### Horizontal composition of extensions of ordinary maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  {f : A → B} {g : A → C} {h : A → X}
  {i : B → C} {j : C → X}
  where

  is-extension-comp-horizontal :
    (I : is-extension f g i) → is-extension g h j → is-extension f h (j ∘ i)
  is-extension-comp-horizontal I J x = (J x) ∙ ap j (I x)
```

## Properties

### The total type of extensions is equivalent to `B → X`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  inv-compute-total-extension :
    {X : UU l3} → total-extension i X ≃ (B → X)
  inv-compute-total-extension = inv-compute-total-extension-dependent-type i

  compute-total-extension :
    {X : UU l3} → (B → X) ≃ total-extension i X
  compute-total-extension = compute-total-extension-dependent-type i
```

## Examples

### The identity is an extension of every map along themselves

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-extension-along-self : is-extension f f id
  is-extension-along-self = refl-htpy

  extension-along-self : extension f f
  extension-along-self = id , is-extension-along-self
```

## See also

- [`orthogonal-factorization-systems.lifts-maps`](orthogonal-factorization-systems.lifts-maps.md)
  for the dual notion.
