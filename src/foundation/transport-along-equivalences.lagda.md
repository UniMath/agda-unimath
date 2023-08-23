# Transport along equivalences

```agda
module foundation.transport-along-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalence-induction
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Applying
[transport along identifications](foundation-core.transport-along-identifications.md)
to [identifications](foundation-core.identity-types.md) arising from the
[univalence axiom](foundation.univalence.md) gives us **transport along
equivalences**.

Since transport defines [equivalences](foundation-core.equivalences.md) of
[fibers](foundation-core.fibers-of-maps.md), this gives us an _action on
equivalences_. Alternatively, we could apply the
[action on identifications](foundation.action-on-identifications-functions.md)
to get another
[action on equivalences](foundation.action-on-equivalences-functions.md), but
luckily, these two notions coincide.

## Definition

```agda
tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X → f Y
tr-equiv f {X} {Y} e = tr f (eq-equiv X Y e)
```

## Properties

### Transport along an equivalence is an equivalence

```agda
is-equiv-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → is-equiv (tr-equiv f e)
is-equiv-tr-equiv f {X} {Y} e = is-equiv-tr f (eq-equiv X Y e)

equiv-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X ≃ f Y
pr1 (equiv-tr-equiv f e) = tr-equiv f e
pr2 (equiv-tr-equiv f e) = is-equiv-tr-equiv f e
```

### Transporting along `id-equiv` is the identity equivalence

```agda
compute-tr-equiv-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X : UU l1} →
  tr-equiv f id-equiv ＝ id
compute-tr-equiv-id-equiv f {X} = ap (tr f) (compute-eq-equiv-id-equiv X)

compute-equiv-tr-equiv-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X : UU l1} →
  equiv-tr-equiv f id-equiv ＝ id-equiv
compute-equiv-tr-equiv-id-equiv f {X} =
  (ap (equiv-tr f) (compute-eq-equiv-id-equiv X)) ∙ (equiv-tr-refl f)
```

### Transport along equivalences preserves composition of equivalences

```agda
distributive-tr-equiv-equiv-comp :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y Z : UU l1} (e : X ≃ Y) (e' : Y ≃ Z) →
  tr-equiv f (e' ∘e e) ~ (tr-equiv f e' ∘ tr-equiv f e)
distributive-tr-equiv-equiv-comp f {X} {Y} {Z} e e' x =
  ( ap (λ p → tr f p x) (inv (compute-eq-equiv-equiv-comp X Y Z e e'))) ∙
  ( tr-concat (eq-equiv X Y e) (eq-equiv Y Z e') x)

distributive-equiv-tr-equiv-equiv-comp :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y Z : UU l1} (e : X ≃ Y) (e' : Y ≃ Z) →
  equiv-tr-equiv f (e' ∘e e) ＝ (equiv-tr-equiv f e' ∘e equiv-tr-equiv f e)
distributive-equiv-tr-equiv-equiv-comp f {X} {Y} {Z} e e' =
  eq-htpy-equiv (distributive-tr-equiv-equiv-comp f e e')
```

### Transporting along an equivalence and its inverse is just the identity

```agda
is-section-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) →
  (tr-equiv f (inv-equiv e) ∘ tr-equiv f e) ~ id
is-section-tr-equiv f {X} {Y} e x =
  ( ap
    ( λ p → tr f p (tr-equiv f e x))
    ( inv (commutativity-inv-eq-equiv X Y e))) ∙
  ( is-section-tr f (eq-equiv X Y e) x)

is-retraction-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) →
  (tr-equiv f e ∘ tr-equiv f (inv-equiv e)) ~ id
is-retraction-tr-equiv f {X} {Y} e x =
  ( ap
    ( tr-equiv f e ∘ (λ p → tr f p x))
    ( inv (commutativity-inv-eq-equiv X Y e))) ∙
  ( is-retraction-tr f (eq-equiv X Y e) x)
```

### Transposing transport along the inverse of an equivalence

```agda
eq-transpose-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) {u : f X} {v : f Y} →
  v ＝ tr-equiv f e u → tr-equiv f (inv-equiv e) v ＝ u
eq-transpose-tr-equiv f e {u} p =
  (ap (tr-equiv f (inv-equiv e)) p) ∙ (is-section-tr-equiv f e u)

eq-transpose-tr-equiv' :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) {u : f X} {v : f Y} →
  tr-equiv f e u ＝ v → u ＝ tr-equiv f (inv-equiv e) v
eq-transpose-tr-equiv' f e {u} p =
  (inv (is-section-tr-equiv f e u)) ∙ (ap (tr-equiv f (inv-equiv e)) p)
```

### Substitution law for transport along equivalences

```agda
substitution-tr-equiv :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → tr-equiv g (ap-equiv f e) ~ tr-equiv (g ∘ f) e
substitution-tr-equiv g f {X} {Y} e X' =
  ( ap (λ p → tr g p X') (is-retraction-eq-equiv (ap-eq-equiv f e))) ∙
  ( substitution-tr g f (eq-equiv X Y e))

substitution-equiv-tr-equiv :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → equiv-tr-equiv g (ap-equiv f e) ＝ equiv-tr-equiv (g ∘ f) e
substitution-equiv-tr-equiv g f e = eq-htpy-equiv (substitution-tr-equiv g f e)
```

### Transporting along the action on equivalences of a function

```agda
compute-tr-equiv-ap-equiv :
  {l1 l2 l3 l4 : Level} {B : UU l1 → UU l2} {D : UU l3 → UU l4}
  (f : UU l1 → UU l3) (g : (X : UU l1) → B X → D (f X))
  {X Y : UU l1} (e : X ≃ Y) (X' : B X) →
  tr-equiv D (ap-equiv f e) (g X X') ＝ g Y (tr-equiv B e X')
compute-tr-equiv-ap-equiv {D = D} f g {X} {Y} e X' =
  ( ap (λ p → tr D p (g X X')) (is-retraction-eq-equiv (ap-eq-equiv f e))) ∙
  ( tr-ap f g (eq-equiv X Y e) X')
```

### Transport along equivalences and the action on equivalences in the universe coincide

```agda
eq-equiv-tr-equiv-ap-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  (e : X ≃ Y) → equiv-tr-equiv f e ＝ ap-equiv f e
eq-equiv-tr-equiv-ap-equiv f {X} =
    ind-equiv X
      ( λ Y e → equiv-tr-equiv f e ＝ ap-equiv f e)
      ( compute-equiv-tr-equiv-id-equiv f ∙ inv (compute-ap-equiv-id-equiv f X))

eq-tr-equiv-map-ap-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  (e : X ≃ Y) → tr-equiv f e ＝ map-equiv (ap-equiv f e)
eq-tr-equiv-map-ap-equiv f e = ap pr1 (eq-equiv-tr-equiv-ap-equiv f e)
```
