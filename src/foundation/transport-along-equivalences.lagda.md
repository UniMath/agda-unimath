# Transport along equivalences

```agda
module foundation.transport-along-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
```

</details>

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
equiv-tr-equiv-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X : UU l1} →
  equiv-tr-equiv f id-equiv ＝ id-equiv
equiv-tr-equiv-id-equiv f {X} =
  (ap (equiv-tr f) (compute-eq-equiv-id-equiv X)) ∙ (equiv-tr-refl f)
```

### Transport along equivalences preserves composition of equivalences

```agda
tr-equiv-equiv-comp :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y Z : UU l1} (e : X ≃ Y) (e' : Y ≃ Z) →
  tr-equiv f (e' ∘e e) ~ (tr-equiv f e' ∘ tr-equiv f e)
tr-equiv-equiv-comp f {X} {Y} {Z} e e' x =
  ( ap (λ p → tr f p x) (inv (compute-eq-equiv-equiv-comp X Y Z e e'))) ∙
  ( tr-concat (eq-equiv X Y e) (eq-equiv Y Z e') x)
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
tr-equiv-subst :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → tr-equiv g (ap-equiv f e) ~ tr-equiv (g ∘ f) e
tr-equiv-subst g f {X} {Y} e X' =
  ( ap (λ p → tr g p X') (is-retraction-eq-equiv (ap-eq-equiv f e))) ∙
  ( tr-subst g f (eq-equiv X Y e))
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
