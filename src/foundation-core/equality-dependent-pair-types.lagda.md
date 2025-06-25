# Equality of dependent pair types

```agda
module foundation-core.equality-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retracts-of-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

An identification `(pair x y) ＝ (pair x' y')` in a dependent pair type `Σ A B`
is equivalently described as a pair `pair α β` consisting of an identification
`α : x ＝ x'` and an identification `β : (tr B α y) ＝ y'`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-Σ : (s t : Σ A B) → UU (l1 ⊔ l2)
  Eq-Σ s t =
    Σ (pr1 s ＝ pr1 t) (λ α → dependent-identification B α (pr2 s) (pr2 t))
```

## Properties

### The type `Id s t` is equivalent to `Eq-Σ s t` for any `s t : Σ A B`

```agda
  refl-Eq-Σ : (s : Σ A B) → Eq-Σ s s
  refl-Eq-Σ s = refl , refl

  eq-base-eq-pair : {s t : Σ A B} → s ＝ t → pr1 s ＝ pr1 t
  eq-base-eq-pair = ap pr1

  dependent-identification-eq-pair :
    {s t : Σ A B} (p : s ＝ t) →
    dependent-identification B (eq-base-eq-pair p) (pr2 s) (pr2 t)
  dependent-identification-eq-pair {s} p = tr-ap pr1 (λ x _ → pr2 x) p (pr1 s)

  pair-eq-Σ : {s t : Σ A B} → s ＝ t → Eq-Σ s t
  pair-eq-Σ p = eq-base-eq-pair p , dependent-identification-eq-pair p

  eq-pair-eq-base :
    {x y : A} {s : B x} (p : x ＝ y) → (x , s) ＝ (y , tr B p s)
  eq-pair-eq-base refl = refl

  eq-pair-eq-base' :
    {x y : A} {t : B y} (p : x ＝ y) → (x , tr B (inv p) t) ＝ (y , t)
  eq-pair-eq-base' refl = refl

  eq-pair-eq-fiber :
    {x : A} {s t : B x} → s ＝ t → (x , s) ＝ (x , t)
  eq-pair-eq-fiber {x} = ap {B = Σ A B} (pair x)

  eq-pair-Σ :
    {s t : Σ A B}
    (α : pr1 s ＝ pr1 t) →
    dependent-identification B α (pr2 s) (pr2 t) → s ＝ t
  eq-pair-Σ refl = eq-pair-eq-fiber

  eq-pair-Σ' : {s t : Σ A B} → Eq-Σ s t → s ＝ t
  eq-pair-Σ' p = eq-pair-Σ (pr1 p) (pr2 p)

  ap-pr1-eq-pair-eq-fiber :
    {x : A} {s t : B x} (p : s ＝ t) → ap pr1 (eq-pair-eq-fiber p) ＝ refl
  ap-pr1-eq-pair-eq-fiber refl = refl

  is-retraction-pair-eq-Σ :
    (s t : Σ A B) → pair-eq-Σ {s} {t} ∘ eq-pair-Σ' {s} {t} ~ id {A = Eq-Σ s t}
  is-retraction-pair-eq-Σ (x , y) (.x , .y) (refl , refl) = refl

  is-section-pair-eq-Σ :
    (s t : Σ A B) → eq-pair-Σ' {s} {t} ∘ pair-eq-Σ {s} {t} ~ id
  is-section-pair-eq-Σ (x , y) .(x , y) refl = refl

  abstract
    is-equiv-eq-pair-Σ : (s t : Σ A B) → is-equiv (eq-pair-Σ' {s} {t})
    is-equiv-eq-pair-Σ s t =
      is-equiv-is-invertible
        ( pair-eq-Σ)
        ( is-section-pair-eq-Σ s t)
        ( is-retraction-pair-eq-Σ s t)

  equiv-eq-pair-Σ : (s t : Σ A B) → Eq-Σ s t ≃ (s ＝ t)
  pr1 (equiv-eq-pair-Σ s t) = eq-pair-Σ'
  pr2 (equiv-eq-pair-Σ s t) = is-equiv-eq-pair-Σ s t

  abstract
    is-equiv-pair-eq-Σ : (s t : Σ A B) → is-equiv (pair-eq-Σ {s} {t})
    is-equiv-pair-eq-Σ s t =
      is-equiv-is-invertible
        ( eq-pair-Σ')
        ( is-retraction-pair-eq-Σ s t)
        ( is-section-pair-eq-Σ s t)

  equiv-pair-eq-Σ : (s t : Σ A B) → (s ＝ t) ≃ Eq-Σ s t
  equiv-pair-eq-Σ s t = (pair-eq-Σ , is-equiv-pair-eq-Σ s t)

  retract-pair-eq-Σ : (s t : Σ A B) → (s ＝ t) retract-of (Eq-Σ s t)
  retract-pair-eq-Σ s t = (pair-eq-Σ , eq-pair-Σ' , is-section-pair-eq-Σ s t)

  η-pair : (t : Σ A B) → (pr1 t , pr2 t) ＝ t
  η-pair t = refl
```

### Lifting equality to the total space

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  lift-eq-Σ :
    {x y : A} (p : x ＝ y) (b : B x) → (x , b) ＝ (y , tr B p b)
  lift-eq-Σ refl b = refl
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
  {B : A → UU l2} {b0 : B a0} {b1 : B a1} (C : Σ A B → UU l3)
  (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) (u : C (a0 , b0)) →
  tr C (eq-pair-Σ p q) u ＝
  tr (λ x → C (a1 , x)) q (tr C (eq-pair-Σ p refl) u)
tr-eq-pair-Σ C refl refl u = refl
```

### The action of `pr1` on identifcations of the form `eq-pair-Σ`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  ap-pr1-eq-pair-Σ :
    {x x' : A} {y : B x} {y' : B x'}
    (p : x ＝ x') (q : dependent-identification B p y y') →
    ap pr1 (eq-pair-Σ p q) ＝ p
  ap-pr1-eq-pair-Σ refl refl = refl
```

### Transport in `B` along the first projection of an identification in `Σ A B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  tr-eq-Σ : {x y : Σ A B} (p : x ＝ y) → tr B (ap pr1 p) (pr2 x) ＝ pr2 y
  tr-eq-Σ refl = refl
```

## See also

- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
- Equality proofs in the fiber of a map are characterized in
  [`foundation.equality-fibers-of-maps`](foundation.equality-fibers-of-maps.md).
