# Cartesian product types

```agda
module foundation.cartesian-product-types where

open import foundation-core.cartesian-product-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.transport
```

</details>

## Properties

### Transport in a family of cartesian products

```agda
tr-prod :
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A}
  (B C : A → UU l2) (p : a0 ＝ a1) (u : B a0 × C a0) →
  (tr (λ a → B a × C a) p u) ＝ (pair (tr B p (pr1 u)) (tr C p (pr2 u)))
tr-prod B C refl u = refl
```

### Transport in a family over a cartesian product

#### Computing transport along a path of the form `eq-pair`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B}
  where

  tr-eq-pair :
    (C : A × B → UU l3) (p : a0 ＝ a1) (q : b0 ＝ b1) (u : C (a0 , b0)) →
    tr C (eq-pair p q) u ＝
    tr (λ x → C (a1 , x)) q (tr (λ x → C (x , b0)) p u)
  tr-eq-pair C refl refl u = refl
```

#### Computing transport along a path of the form `eq-pair` When one of the paths is `refl`

```agda
  left-unit-law-tr-eq-pair :
    (C : A × B → UU l3) (q : b0 ＝ b1) (u : C (a0 , b0)) →
    (tr C (eq-pair refl q) u) ＝ tr (λ x → C (a0 , x)) q u
  left-unit-law-tr-eq-pair C refl u = refl

  right-unit-law-tr-eq-pair :
    (C : A × B → UU l3) (p : a0 ＝ a1) (u : C (a0 , b0)) →
    (tr C (eq-pair p refl) u) ＝ tr (λ x → C (x , b0)) p u
  right-unit-law-tr-eq-pair C refl u = refl
```

#### Computing transport along a path of the form `eq-pair` when both paths are identical

```agda
tr-eq-pair-diagonal :
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} (C : A × A → UU l2)
  (p : a0 ＝ a1) (u : C (a0 , a0)) →
  tr C (eq-pair p p) u ＝ tr (λ a → C (a , a)) p u
tr-eq-pair-diagonal C refl u = refl
```

### Subuniverses closed under cartesian product types

```agda
is-closed-under-products-subuniverses :
  {l1 l2 l3 l4 l5 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (R : subuniverse (l1 ⊔ l3) l5) → UU (lsuc l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
is-closed-under-products-subuniverses {l1} {l2} {l3} P Q R =
  {X : UU l1} {Y : UU l3} →
  is-in-subuniverse P X → is-in-subuniverse Q Y → is-in-subuniverse R (X × Y)

is-closed-under-products-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
is-closed-under-products-subuniverse P =
  is-closed-under-products-subuniverses P P P
```
