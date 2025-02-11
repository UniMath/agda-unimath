# Transport along equivalences

```agda
module foundation.transport-along-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-functions
open import foundation.action-on-equivalences-type-families
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalence-induction
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

Given a map between universes `f : 𝒰 → 𝒱`, applying
[transport along identifications](foundation-core.transport-along-identifications.md)
to [identifications](foundation-core.identity-types.md) arising from the
[univalence axiom](foundation.univalence.md) gives us
{{#concept "transport along equivalences" Agda=tr-equiv}}:

```text
  tr-equiv f : X ≃ Y → f X ≃ f Y.
```

Alternatively, we could apply the
[action on identifications](foundation.action-on-identifications-functions.md)
to get another
[action on equivalences](foundation.action-on-equivalences-functions.md).
However, by univalence such a map must also be unique, hence these two
constructions coincide.

## Definitions

### Transporting along equivalences

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  where

  map-tr-equiv : X ≃ Y → f X → f Y
  map-tr-equiv e = tr f (eq-equiv e)

  abstract
    is-equiv-map-tr-equiv : (e : X ≃ Y) → is-equiv (map-tr-equiv e)
    is-equiv-map-tr-equiv e = is-equiv-tr f (eq-equiv e)

  tr-equiv : X ≃ Y → f X ≃ f Y
  pr1 (tr-equiv e) = map-tr-equiv e
  pr2 (tr-equiv e) = is-equiv-map-tr-equiv e

  eq-tr-equiv : X ≃ Y → f X ＝ f Y
  eq-tr-equiv = eq-equiv ∘ tr-equiv
```

### Transporting along inverse equivalences

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  where

  map-tr-inv-equiv : X ≃ Y → f Y → f X
  map-tr-inv-equiv e = tr f (eq-equiv (inv-equiv e))

  abstract
    is-equiv-map-tr-inv-equiv : (e : X ≃ Y) → is-equiv (map-tr-inv-equiv e)
    is-equiv-map-tr-inv-equiv e = is-equiv-tr f (eq-equiv (inv-equiv e))

  tr-inv-equiv : X ≃ Y → f Y ≃ f X
  pr1 (tr-inv-equiv e) = map-tr-inv-equiv e
  pr2 (tr-inv-equiv e) = is-equiv-map-tr-inv-equiv e

  eq-tr-inv-equiv : X ≃ Y → f Y ＝ f X
  eq-tr-inv-equiv = eq-equiv ∘ tr-inv-equiv
```

## Properties

### Transporting along `id-equiv` is the identity equivalence

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2) {X : UU l1}
  where

  compute-map-tr-equiv-id-equiv : map-tr-equiv f id-equiv ＝ id
  compute-map-tr-equiv-id-equiv = ap (tr f) (compute-eq-equiv-id-equiv X)

  compute-tr-equiv-id-equiv : tr-equiv f id-equiv ＝ id-equiv
  compute-tr-equiv-id-equiv =
    is-injective-map-equiv (ap (tr f) (compute-eq-equiv-id-equiv X))
```

### Transport along equivalences preserves composition of equivalences

For any operation `f : 𝒰₁ → 𝒰₂` and any two composable equivalences `e : X ≃ Y`
and `e' : Y ≃ Z` in `𝒰₁` we obtain a commuting triangle

```text
                     tr-equiv f e
                 f X ----------> f Y
                     \         /
  tr-equiv f (e' ∘ e) \       / tr-equiv f e'
                       \     /
                        ∨   ∨
                         f Z
```

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y Z : UU l1} (e : X ≃ Y) (e' : Y ≃ Z)
  where

  distributive-map-tr-equiv-equiv-comp :
    coherence-triangle-maps
      ( map-tr-equiv f (e' ∘e e))
      ( map-tr-equiv f e')
      ( map-tr-equiv f e)
  distributive-map-tr-equiv-equiv-comp x =
    ( inv (ap (λ p → tr f p x) (compute-eq-equiv-comp-equiv e e'))) ∙
    ( tr-concat (eq-equiv e) (eq-equiv e') x)

  distributive-tr-equiv-equiv-comp :
    tr-equiv f (e' ∘e e) ＝ tr-equiv f e' ∘e tr-equiv f e
  distributive-tr-equiv-equiv-comp =
    eq-htpy-equiv distributive-map-tr-equiv-equiv-comp
```

### Transporting along an inverse equivalence is inverse to transporting along the original equivalence

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y)
  where

  is-section-map-tr-inv-equiv :
    is-section (map-tr-equiv f e) (map-tr-equiv f (inv-equiv e))
  is-section-map-tr-inv-equiv x =
    ( inv
      ( ap
        ( map-tr-equiv f e ∘ (λ p → tr f p x))
        ( commutativity-inv-eq-equiv e))) ∙
    ( is-section-inv-tr f (eq-equiv e) x)

  is-retraction-map-tr-inv-equiv :
    is-retraction (map-tr-equiv f e) (map-tr-equiv f (inv-equiv e))
  is-retraction-map-tr-inv-equiv x =
    ( inv
      ( ap
        ( λ p → tr f p (map-tr-equiv f e x))
        ( commutativity-inv-eq-equiv e))) ∙
    ( is-retraction-inv-tr f (eq-equiv e) x)
```

### Transposing transport along the inverse of an equivalence

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) {u : f X} {v : f Y}
  where

  eq-transpose-map-tr-equiv :
    v ＝ map-tr-equiv f e u → map-tr-equiv f (inv-equiv e) v ＝ u
  eq-transpose-map-tr-equiv p =
    ap (map-tr-equiv f (inv-equiv e)) p ∙ is-retraction-map-tr-inv-equiv f e u

  eq-transpose-map-tr-equiv' :
    map-tr-equiv f e u ＝ v → u ＝ map-tr-equiv f (inv-equiv e) v
  eq-transpose-map-tr-equiv' p =
    ( inv (is-retraction-map-tr-inv-equiv f e u)) ∙
    ( ap (map-tr-equiv f (inv-equiv e)) p)
```

### Substitution law for transport along equivalences

```agda
module _
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y)
  where

  substitution-map-tr-equiv :
    map-tr-equiv g (action-equiv-family f e) ~ map-tr-equiv (g ∘ f) e
  substitution-map-tr-equiv X' =
    ( ap
      ( λ p → tr g p X')
      ( is-retraction-eq-equiv (action-equiv-function f e))) ∙
    ( substitution-law-tr g f (eq-equiv e))

  substitution-law-tr-equiv :
    tr-equiv g (action-equiv-family f e) ＝ tr-equiv (g ∘ f) e
  substitution-law-tr-equiv = eq-htpy-equiv substitution-map-tr-equiv
```

### Transporting along the action on equivalences of a function

```agda
compute-map-tr-equiv-action-equiv-family :
  {l1 l2 l3 l4 : Level} {B : UU l1 → UU l2} {D : UU l3 → UU l4}
  (f : UU l1 → UU l3) (g : (X : UU l1) → B X → D (f X))
  {X Y : UU l1} (e : X ≃ Y) (X' : B X) →
  map-tr-equiv D (action-equiv-family f e) (g X X') ＝ g Y (map-tr-equiv B e X')
compute-map-tr-equiv-action-equiv-family {D = D} f g {X} e X' =
  ( ap
    ( λ p → tr D p (g X X'))
    ( is-retraction-eq-equiv (action-equiv-function f e))) ∙
  ( tr-ap f g (eq-equiv e) X')
```

### Transport along equivalences and the action on equivalences in the universe coincide

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} (e : X ≃ Y)
  where

  eq-tr-equiv-action-equiv-family :
    tr-equiv f e ＝ action-equiv-family f e
  eq-tr-equiv-action-equiv-family =
    ind-equiv
      ( λ Y d → tr-equiv f d ＝ action-equiv-family f d)
      ( compute-tr-equiv-id-equiv f ∙
        inv (compute-action-equiv-family-id-equiv f))
      ( e)

  eq-map-tr-equiv-map-action-equiv-family :
    map-tr-equiv f e ＝ map-action-equiv-family f e
  eq-map-tr-equiv-map-action-equiv-family =
    ap map-equiv eq-tr-equiv-action-equiv-family
```
