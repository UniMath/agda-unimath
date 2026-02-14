# Equality of cartesian product types

```agda
module foundation.equality-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Identifications `Id (pair x y) (pair x' y')` in a cartesian product are
equivalently described as pairs of identifications `Id x x'` and `Id y y'`. This
provides us with a characterization of the identity type of cartesian product
types.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  Eq-product : (s t : A × B) → UU (l1 ⊔ l2)
  Eq-product s t = (pr1 s ＝ pr1 t) × (pr2 s ＝ pr2 t)
```

## Properties

### The type `Eq-product s t` is equivalent to `Id s t`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  eq-pair' : {s t : A × B} → Eq-product s t → s ＝ t
  eq-pair' (p , q) = ap-binary pair p q

  eq-pair : {s t : A × B} → pr1 s ＝ pr1 t → pr2 s ＝ pr2 t → s ＝ t
  eq-pair p q = eq-pair' (p , q)

  pair-eq : {s t : A × B} → s ＝ t → Eq-product s t
  pr1 (pair-eq α) = ap pr1 α
  pr2 (pair-eq α) = ap pr2 α

  is-retraction-pair-eq :
    {s t : A × B} → pair-eq {s} {t} ∘ eq-pair' {s} {t} ~ id
  is-retraction-pair-eq (refl , refl) = refl

  is-section-pair-eq :
    {s t : A × B} → eq-pair' {s} {t} ∘ pair-eq {s} {t} ~ id
  is-section-pair-eq refl = refl

  abstract
    is-equiv-eq-pair :
      (s t : A × B) → is-equiv (eq-pair' {s} {t})
    is-equiv-eq-pair s t =
      is-equiv-is-invertible pair-eq is-section-pair-eq is-retraction-pair-eq

  equiv-eq-pair :
    (s t : A × B) → Eq-product s t ≃ (s ＝ t)
  pr1 (equiv-eq-pair s t) = eq-pair'
  pr2 (equiv-eq-pair s t) = is-equiv-eq-pair s t

  abstract
    is-equiv-pair-eq :
      (s t : A × B) → is-equiv (pair-eq {s} {t})
    is-equiv-pair-eq s t =
      is-equiv-is-invertible eq-pair' is-retraction-pair-eq is-section-pair-eq

  equiv-pair-eq :
    (s t : A × B) → (s ＝ t) ≃ Eq-product s t
  pr1 (equiv-pair-eq s t) = pair-eq
  pr2 (equiv-pair-eq s t) = is-equiv-pair-eq s t
```

### Commuting triangles for `eq-pair`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  triangle-eq-pair :
    {a0 a1 : A} {b0 b1 : B} (p : a0 ＝ a1) (q : b0 ＝ b1) →
    eq-pair p q ＝ eq-pair p refl ∙ eq-pair refl q
  triangle-eq-pair refl q = refl

  triangle-eq-pair' :
    {a0 a1 : A} {b0 b1 : B} (p : a0 ＝ a1) (q : b0 ＝ b1) →
    eq-pair p q ＝ eq-pair refl q ∙ eq-pair p refl
  triangle-eq-pair' p refl = refl
```

### `eq-pair` preserves concatenation

```agda
eq-pair-concat :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x x' x'' : A} {y y' y'' : B}
  (p : x ＝ x') (p' : x' ＝ x'') (q : y ＝ y') (q' : y' ＝ y'') →
  eq-pair (p ∙ p') (q ∙ q') ＝ eq-pair p q ∙ eq-pair p' q'
eq-pair-concat refl p' refl q' = refl
```

### `eq-pair` computes in the expected way when the action on paths of the projections is applies

```agda
ap-pr1-eq-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
  ap pr1 (eq-pair p q) ＝ p
ap-pr1-eq-pair refl refl = refl

ap-pr2-eq-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
  ap pr2 (eq-pair p q) ＝ q
ap-pr2-eq-pair refl refl = refl
```

###

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x : A} {y y' : B x}
  where

  ap-pr1-ap-pair :
    (p : y ＝ y') → ap pr1 (ap (pair {B = B} x) p) ＝ refl
  ap-pr1-ap-pair refl = refl

  inv-ap-pr1-ap-pair :
    (p : y ＝ y') → refl ＝ ap pr1 (ap (pair {B = B} x) p)
  inv-ap-pr1-ap-pair p = inv (ap-pr1-ap-pair p)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x : A} {y y' : B}
  where

  ap-pr2-ap-pair : (p : y ＝ y') → ap pr2 (ap (pair {B = λ _ → B} x) p) ＝ p
  ap-pr2-ap-pair refl = refl

  inv-ap-pr2-ap-pair : (p : y ＝ y') → p ＝ ap pr2 (ap (pair {B = λ _ → B} x) p)
  inv-ap-pr2-ap-pair p = inv (ap-pr2-ap-pair p)
```

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
    tr C (eq-pair refl q) u ＝ tr (λ x → C (a0 , x)) q u
  left-unit-law-tr-eq-pair C refl u = refl

  right-unit-law-tr-eq-pair :
    (C : A × B → UU l3) (p : a0 ＝ a1) (u : C (a0 , b0)) →
    tr C (eq-pair p refl) u ＝ tr (λ x → C (x , b0)) p u
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

## See also

- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
- Equality proofs in dependent product types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
- Equality proofs in coproduct types are characterized in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).
