# Maps with double negation dense equality

```agda
module foundation.double-negation-dense-equality-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.double-negation-dense-equality
open import foundation.embeddings
open import foundation.function-types
open import foundation.irrefutable-equality
open import foundation.iterating-functions
open import foundation.propositional-maps
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.propositions
```

</details>

## Idea

A map `f : A → B` is said to have
{{#concept "double negation dense equality" Disambiguation="map of types" Agda=has-double-negation-dense-equality-map}}
if its [fibers](foundation-core.fibers-of-maps.md) have
[double negation dense equality](foundation.irrefutable-equality.md). I.e., if
for every `y : B` and every pair `p q : fiber f y` it is
[irrefutable](foundation.irrefutable-propositions.md) that `p` equals `q`. In
other words, `¬¬ (p ＝ q)` holds.

## Definitions

```agda
has-double-negation-dense-equality-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
has-double-negation-dense-equality-map {B = B} f =
  (y : B) → has-double-negation-dense-equality (fiber f y)
```

## Properties

### Embeddings have double negation dense equality

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    has-double-negation-dense-equality-map-is-prop-map :
      is-prop-map f → has-double-negation-dense-equality-map f
    has-double-negation-dense-equality-map-is-prop-map H b x y =
      irrefutable-eq-eq (eq-is-prop (H b))

  abstract
    has-double-negation-dense-equality-map-is-emb :
      is-emb f → has-double-negation-dense-equality-map f
    has-double-negation-dense-equality-map-is-emb H =
      has-double-negation-dense-equality-map-is-prop-map
        ( is-prop-map-is-emb H)

has-double-negation-dense-equality-map-id :
  {l : Level} {A : UU l} →
  has-double-negation-dense-equality-map (id {A = A})
has-double-negation-dense-equality-map-id =
  has-double-negation-dense-equality-map-is-emb is-emb-id
```

### Composition of maps with double negation dense equality

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  abstract
    has-double-negation-dense-equality-map-comp :
      has-double-negation-dense-equality-map g →
      has-double-negation-dense-equality-map f →
      has-double-negation-dense-equality-map (g ∘ f)
    has-double-negation-dense-equality-map-comp G F y =
      has-double-negation-dense-equality-equiv
        ( compute-fiber-comp g f y)
        ( has-double-negation-dense-equality-Σ (G y) (F ∘ pr1))

module _
  {l1 : Level} {A : UU l1} {f : A → A}
  (F : has-double-negation-dense-equality-map f)
  where

  abstract
    has-double-negation-dense-equality-map-iterate :
      (n : ℕ) → has-double-negation-dense-equality-map (iterate n f)
    has-double-negation-dense-equality-map-iterate zero-ℕ =
      has-double-negation-dense-equality-map-id
    has-double-negation-dense-equality-map-iterate (succ-ℕ n) =
      has-double-negation-dense-equality-map-comp F
        ( has-double-negation-dense-equality-map-iterate n)
```
