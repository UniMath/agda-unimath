# Transport

```agda
module foundation.transport where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Properties

### Transport

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2}
  {x0 x1 : X} (p : x0 ＝ x1)
  where

  preserves-tr-id :
    (p : x0 ＝ x1) → preserves-tr (λ x → id {A = A x}) p ~ refl-htpy
  preserves-tr-id refl = refl-htpy
```

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
  (p : a0 ＝ a1) (u : C (a0 , a0)) → (tr C (eq-pair p p) u) ＝ (tr (λ a → C (a , a)) p u)
tr-eq-pair-diagonal C refl u = refl
```

### Transport in a family of dependent pair types

```agda
tr-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) (p : a0 ＝ a1) (z : Σ (B a0) (λ x → C a0 x)) →
  tr (λ a → (Σ (B a) (C a))) p z ＝
  pair (tr B p (pr1 z)) (tr (ind-Σ C) (eq-pair-Σ p refl) (pr2 z))
tr-Σ C refl z = refl
```

### Transport in a family over a dependent pair type

```agda
tr-eq-pair-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A}
  {B : A → UU l2} {b0 : B a0} {b1 : B a1} (C : (Σ A (λ a → B a)) → UU l3)
  (p : a0 ＝ a1) (q : path-over (B) p b0 b1) (u : C (a0 , b0)) →
  tr C (eq-pair-Σ p q) u ＝
  tr (λ x → C (a1 , x)) q (tr C (eq-pair-Σ p refl) u)
tr-eq-pair-Σ C refl refl u = refl
```

### Transport in a family of function types

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {x y : A} (B : A → UU l2) (C : A → UU l3)
  where

  tr-function-type :
    (p : x ＝ y) (f : B x → C x) →
    tr (λ a → B a → C a) p f ＝ (tr C p ∘ (f ∘ tr B (inv p)))
  tr-function-type refl f = refl

  compute-path-over-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ((b : B x) → tr C p (f b) ＝ g (tr B p b)) ≃
    (tr (λ a → B a → C a) p f ＝ g)
  compute-path-over-function-type refl f g = inv-equiv equiv-funext

  map-compute-path-over-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ((b : B x) → tr C p (f b) ＝ g (tr B p b)) →
    (tr (λ a → B a → C a) p f ＝ g)
  map-compute-path-over-function-type p f g =
    map-equiv (compute-path-over-function-type p f g)
```

Relation between`compute-path-over-function-type` and `preserves-tr`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {i0 i1 : I} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i)
  where

  preserves-tr-apd-function :
    (p : i0 ＝ i1) (a : A i0) →
    (map-inv-equiv (compute-path-over-function-type
      A B p (f i0) (f i1)) (apd f p) a) ＝
    inv-htpy (preserves-tr f p) a
  preserves-tr-apd-function refl = refl-htpy
```

### Transport in identity types

```agda
tr-fx＝gy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {a0 a1 : A} {b0 b1 : B} (f : A → C) (g : B → C)
  (p : a0 ＝ a1) (q : b0 ＝ b1) (s : f a0 ＝ g b0) →
  (tr (λ z → (f (pr1 z)) ＝ (g (pr2 z))) (eq-pair p q) s) ＝
  (((inv (ap f p)) ∙ s) ∙ (ap g q))
tr-fx＝gy f g refl refl s = inv right-unit

tr-x＝y :
  {l1 : Level} {A : UU l1} {a0 a1 a2 a3 : A}
  (p : a0 ＝ a1) (q : a2 ＝ a3) (s : a0 ＝ a2) →
  (tr (λ z → (pr1 z) ＝ (pr2 z)) (eq-pair p q) s) ＝ ((inv p) ∙ (s ∙ q))
tr-x＝y refl refl s = inv right-unit
```

### Transport in the family of loops

```agda
tr-loop :
  {l1 : Level} {A : UU l1} {a0 a1 : A} (p : a0 ＝ a1) (l : a0 ＝ a0) →
  (tr (λ y → y ＝ y) p l) ＝ (((inv p) ∙ l) ∙ p)
tr-loop refl l = inv right-unit
```
