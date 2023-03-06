# Equality of dependent pair types

```agda
{-# OPTIONS --safe #-}
```

<details><summary>Imports</summary>
```agda
module foundation-core.equality-dependent-pair-types where
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels
```
</details>

## Idea

An identification `(pair x y) ＝ (pair x' y')` in a dependent pair type `Σ A B` is equivalently described as a pair `pair α β` consisting of an identification `α : x ＝ x'` and an identification `β : (tr B α y) ＝ y'`.

## Definition

```agda

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-Σ : (s t : Σ A B) → UU (l1 ⊔ l2)
  Eq-Σ s t = Σ (pr1 s ＝ pr1 t) (λ α → tr B α (pr2 s) ＝ pr2 t)
```

## Properties

### The type `Id s t` is equivalent to `Eq-Σ s t` for any `s t : Σ A B`.

```agda
  refl-Eq-Σ : (s : Σ A B) → Eq-Σ s s
  pr1 (refl-Eq-Σ (pair a b)) = refl
  pr2 (refl-Eq-Σ (pair a b)) = refl

  pair-eq-Σ : {s t : Σ A B} → s ＝ t → Eq-Σ s t
  pair-eq-Σ {s} refl = refl-Eq-Σ s

  eq-pair-Σ :
    {s t : Σ A B} →
    (α : pr1 s ＝ pr1 t) → tr B α (pr2 s) ＝ pr2 t → s ＝ t
  eq-pair-Σ {pair x y} {pair .x .y} refl refl = refl

  eq-pair-Σ' : {s t : Σ A B} → Eq-Σ s t → s ＝ t
  eq-pair-Σ' p = eq-pair-Σ (pr1 p) (pr2 p)

  isretr-pair-eq-Σ :
    (s t : Σ A B) →
    ((pair-eq-Σ {s} {t}) ∘ (eq-pair-Σ' {s} {t})) ~ id {A = Eq-Σ s t}
  isretr-pair-eq-Σ (pair x y) (pair .x .y) (pair refl refl) = refl

  issec-pair-eq-Σ :
    (s t : Σ A B) → ((eq-pair-Σ' {s} {t}) ∘ (pair-eq-Σ {s} {t})) ~ id
  issec-pair-eq-Σ (pair x y) .(pair x y) refl = refl

  abstract
    is-equiv-eq-pair-Σ : (s t : Σ A B) → is-equiv (eq-pair-Σ' {s} {t})
    is-equiv-eq-pair-Σ s t =
      is-equiv-has-inverse
        ( pair-eq-Σ)
        ( issec-pair-eq-Σ s t)
        ( isretr-pair-eq-Σ s t)

  equiv-eq-pair-Σ : (s t : Σ A B) → Eq-Σ s t ≃ (s ＝ t)
  equiv-eq-pair-Σ s t = pair eq-pair-Σ' (is-equiv-eq-pair-Σ s t)

  abstract
    is-equiv-pair-eq-Σ : (s t : Σ A B) → is-equiv (pair-eq-Σ {s} {t})
    is-equiv-pair-eq-Σ s t =
      is-equiv-has-inverse
        ( eq-pair-Σ')
        ( isretr-pair-eq-Σ s t)
        ( issec-pair-eq-Σ s t)

  equiv-pair-eq-Σ : (s t : Σ A B) → (s ＝ t) ≃ Eq-Σ s t
  equiv-pair-eq-Σ s t = pair pair-eq-Σ (is-equiv-pair-eq-Σ s t)

  η-pair : (t : Σ A B) → (pair (pr1 t) (pr2 t)) ＝ t
  η-pair t = eq-pair-Σ refl refl
```

### Lifting equality to the total space

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  lift-eq-Σ :
    {x y : A} (p : x ＝ y) (b : B x) → (pair x b) ＝ (pair y (tr B p b))
  lift-eq-Σ refl b = refl
```

## See also

- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
- Equality proofs in the fiber of a map are characterized in
  [`foundation.equality-fibers-of-maps`](foundation.equality-equality-fibers-of-maps.md).
