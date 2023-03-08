# Equality of cartesian product types

```agda
{-# OPTIONS --safe #-}
```

```agda
module foundation-core.equality-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels
```

</details>

## Idea

Identifications `Id (pair x y) (pair x' y')` in a cartesian product are equivalently described as pairs of identifications `Id x x'` and `Id y y'`. This provides us with a characterization of the identity type of cartesian product types.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  Eq-prod : (s t : A × B) → UU (l1 ⊔ l2)
  Eq-prod s t = ((pr1 s) ＝ (pr1 t)) × ((pr2 s) ＝ (pr2 t))
```

## Properties

### The type `Eq-prod s t` is equivalent to `Id s t`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  eq-pair' : {s t : A × B} → Eq-prod s t → s ＝ t
  eq-pair' {pair x y} {pair .x .y} (pair refl refl) = refl

  eq-pair :
    {s t : A × B} → (pr1 s) ＝ (pr1 t) → (pr2 s) ＝ (pr2 t) → s ＝ t
  eq-pair p q = eq-pair' (pair p q)

  pair-eq : {s t : A × B} → s ＝ t → Eq-prod s t
  pr1 (pair-eq α) = ap pr1 α
  pr2 (pair-eq α) = ap pr2 α

  isretr-pair-eq :
    {s t : A × B} → ((pair-eq {s} {t}) ∘ (eq-pair' {s} {t})) ~ id
  isretr-pair-eq {pair x y} {pair .x .y} (pair refl refl) = refl

  issec-pair-eq :
    {s t : A × B} → ((eq-pair' {s} {t}) ∘ (pair-eq {s} {t})) ~ id
  issec-pair-eq {pair x y} {pair .x .y} refl = refl

  abstract
    is-equiv-eq-pair :
      (s t : A × B) → is-equiv (eq-pair' {s} {t})
    is-equiv-eq-pair s t =
      is-equiv-has-inverse pair-eq issec-pair-eq isretr-pair-eq

  equiv-eq-pair :
    (s t : A × B) → Eq-prod s t ≃ (s ＝ t)
  pr1 (equiv-eq-pair s t) = eq-pair'
  pr2 (equiv-eq-pair s t) = is-equiv-eq-pair s t

  abstract
    is-equiv-pair-eq :
      (s t : A × B) → is-equiv (pair-eq {s} {t})
    is-equiv-pair-eq s t =
      is-equiv-has-inverse eq-pair' isretr-pair-eq issec-pair-eq

  equiv-pair-eq :
    (s t : A × B) → (s ＝ t) ≃ Eq-prod s t
  pr1 (equiv-pair-eq s t) = pair-eq
  pr2 (equiv-pair-eq s t) = is-equiv-pair-eq s t
```

## Properties

### Commuting triangles for `eq-pair`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  triangle-eq-pair :
    {a0 a1 : A} {b0 b1 : B} (p : a0 ＝ a1) (q : b0 ＝ b1) →
    eq-pair p q ＝ ((eq-pair p refl) ∙ (eq-pair refl q))
  triangle-eq-pair refl refl = refl

  triangle-eq-pair' :
    {a0 a1 : A} {b0 b1 : B} (p : a0 ＝ a1) (q : b0 ＝ b1) →
    eq-pair p q ＝ ((eq-pair refl q) ∙ (eq-pair p refl))
  triangle-eq-pair' refl refl = refl
```

### `eq-pair` preserves concatenation

```agda
eq-pair-concat :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x x' x'' : A} {y y' y'' : B}
  (p : x ＝ x') (p' : x' ＝ x'') (q : y ＝ y') (q' : y' ＝ y'') →
  ( eq-pair {s = pair x y} {t = pair x'' y''} (p ∙ p') (q ∙ q')) ＝
  ( ( eq-pair {s = pair x y} {t = pair x' y'} p q) ∙
    ( eq-pair p' q'))
eq-pair-concat refl p' refl q' = refl
```

### `eq-pair` computes in the expected way when the action on paths of the projections is applies

```agda
ap-pr1-eq-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
  ap pr1 (eq-pair {s = pair x y} {pair x' y'} p q) ＝ p
ap-pr1-eq-pair refl refl = refl

ap-pr2-eq-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
  ap pr2 (eq-pair {s = pair x y} {pair x' y'} p q) ＝ q
ap-pr2-eq-pair refl refl = refl
```

## See also

- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
- Equality proofs in dependent product types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
- Equality proofs in coproduct types are characterized in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).
