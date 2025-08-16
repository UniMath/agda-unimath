# Maps with double negation dense equality

```agda
module foundation.double-negation-dense-equality-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-negation-dense-equality
open import foundation.irrefutable-equality
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
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
