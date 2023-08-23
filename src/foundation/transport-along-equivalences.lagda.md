# Transport along equivalences

```agda
module foundation.transport-along-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.univalence
open import foundation.action-on-identifications-functions
open import foundation.action-on-equivalences-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation.transport
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
  X ≃ Y → (f X) ≃ (f Y)
pr1 (equiv-tr-equiv f e) = tr-equiv f e
pr2 (equiv-tr-equiv f e) = is-equiv-tr-equiv f e
```

### Transporting along `id-equiv` is the identity equivalence

```agda
equiv-tr-equiv-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X : UU l1} →
  equiv-tr-equiv f id-equiv ＝ id-equiv
equiv-tr-equiv-id-equiv f {X} =
  ap (equiv-tr f) (compute-eq-equiv-id-equiv X) ∙ equiv-tr-refl f
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

### Transposing transport along the inverse of an equivalence

```agda
eq-transpose-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) {u : f X} {v : f Y} →
  v ＝ tr-equiv f e u → tr-equiv f (inv-equiv e) v ＝ u
eq-transpose-tr-equiv f {X} {Y} e {u} {v} p =
  ( ap (tr-equiv f (inv-equiv e)) p) ∙
  ( ( ap
      ( λ q → tr f q (tr-equiv f e u))
      ( inv (commutativity-inv-eq-equiv X Y e))) ∙
    ( is-section-tr f (eq-equiv X Y e) u))

eq-transpose-tr-equiv' :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) {u : f X} {v : f Y} →
  tr-equiv f e u ＝ v → u ＝ tr-equiv f (inv-equiv e) v
eq-transpose-tr-equiv' f {X} {Y} e {u} {v} p =
  ( inv (is-section-tr f (eq-equiv X Y e) u)) ∙
  ( ( ap (tr f (inv (eq-equiv X Y e))) p) ∙
    ( ap (λ q → tr f q v) (commutativity-inv-eq-equiv X Y e)))
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
