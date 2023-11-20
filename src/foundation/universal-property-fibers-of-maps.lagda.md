# The Universal Property of Fibers of Maps

```agda
module foundation.universal-property-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
open import foundation-core.universal-property-pullbacks
```

## Idea

A map `f : A → B` induces a type family `fiber f : B → UU`. By
precomposing with `f`, we have another type family `(fiber f) ∘ f : A → UU`.
This latter type family always has a section given by
`λ a → (a , refl) : (a : A) → fiber f (f a)`.

We can uniquely characterize the family of fibers `fiber f : B → UU` as
the initial type family equipped with such a section. Explicitly,
`fiber f : B → UU` is initial amoung type families `P : B → UU` equipped
with sections `(a : A) → P (f a)`. This can be packaged into an equivalence
between fiberwise maps from `fiber f` to `P` and sections of `B ∘ f`:

```text
((b : B) → fiber f b → P b) ≃ ((a : A) → P (f a))
```

This universal property is especially useful when `A` itself enjoys a mapping
out universal property. This lets us characterize the sections
`(a : A) → B (f a)`. And, in the case that `f` was defined using the mapping out
property of `A`, we may obtain an even nicer characterization.

For example, if we take `A` to be `unit` and the map `f : unit → B` to be
defined by a point `b₀ : B` and the universal property of `unit`,
we have

```text
((b : B) → fiber f b → P b) ≃ ((t : unit) → P (f t)) ≃ ((t : unit) → P b₀) ≃ P b₀
```

which essentialy tells us `fiber f : B → UU` has the same universal property as
`Id b₀ : B → UU`. 

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (F : B → UU l3)
  (δ : (a : A) → F (f a))
  where

  ev-fiber :
    {l4 : Level} (P : B → UU l4) → ((b : B) → F b → P b) →
    (a : A) → P (f a)
  ev-fiber P h a = h (f a) (δ a)

  universal-property-fiber :
    (l4 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
  universal-property-fiber l4 = (P : B → UU l4) → is-equiv (ev-fiber P)
```

## Properties

### Fibers are uniquely unique

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (F : B → UU l3)
  (δ : (a : A) → F (f a)) (F' : B → UU l4) (δ' : (a : A) → F' (f a))
  where

  unique-fiber :
    ({l : Level} → universal-property-fiber f F δ l) →
    ({l : Level} → universal-property-fiber f F' δ' l)  → (b : B) → F b ≃ F' b
  pr1 (unique-fiber u u' b) = (map-inv-is-equiv (u F')) δ' b
  pr2 (unique-fiber u u' b) =
    is-equiv-is-invertible
      ( map-inv-is-equiv (u' F) δ b)
      ( λ x → {!!})
      ( {!!})

```
