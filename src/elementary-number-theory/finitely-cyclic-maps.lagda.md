# Finitely cyclic maps

```agda
module elementary-number-theory.finitely-cyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

```agda
module _
  {l : Level} {X : UU l}
  where

  is-finitely-cyclic-map : (f : X → X) → UU l
  is-finitely-cyclic-map f = (x y : X) → Σ ℕ (λ k → iterate k f x ＝ y)

  length-path-is-finitely-cyclic-map :
    {f : X → X} → is-finitely-cyclic-map f → X → X → ℕ
  length-path-is-finitely-cyclic-map H x y = pr1 (H x y)

  eq-is-finitely-cyclic-map :
    {f : X → X} (H : is-finitely-cyclic-map f) (x y : X) →
    iterate (length-path-is-finitely-cyclic-map H x y) f x ＝ y
  eq-is-finitely-cyclic-map H x y = pr2 (H x y)
```

## Properties

### Finitely cyclic maps are equivalences

```agda
  map-inv-is-finitely-cyclic-map :
    (f : X → X) (H : is-finitely-cyclic-map f) → X → X
  map-inv-is-finitely-cyclic-map f H x =
    iterate (length-path-is-finitely-cyclic-map H (f x) x) f x

  is-section-map-inv-is-finitely-cyclic-map :
    (f : X → X) (H : is-finitely-cyclic-map f) →
    (f ∘ map-inv-is-finitely-cyclic-map f H) ~ id
  is-section-map-inv-is-finitely-cyclic-map f H x =
    ( reassociate-iterate-succ-ℕ
      ( length-path-is-finitely-cyclic-map H (f x) x)
      ( f)
      ( x)) ∙
    ( eq-is-finitely-cyclic-map H (f x) x)

  is-retraction-map-inv-is-finitely-cyclic-map :
    (f : X → X) (H : is-finitely-cyclic-map f) →
    (map-inv-is-finitely-cyclic-map f H ∘ f) ~ id
  is-retraction-map-inv-is-finitely-cyclic-map f H x =
    ( ap
      ( iterate (length-path-is-finitely-cyclic-map H (f (f x)) (f x)) f ∘ f)
      ( inv (eq-is-finitely-cyclic-map H (f x) x))) ∙
    ( ( ap
        ( iterate (length-path-is-finitely-cyclic-map H (f (f x)) (f x)) f)
          ( reassociate-iterate-succ-ℕ
            ( length-path-is-finitely-cyclic-map H (f x) x) f (f x))) ∙
      ( ( iterate-iterate
          ( length-path-is-finitely-cyclic-map H (f (f x)) (f x))
          ( length-path-is-finitely-cyclic-map H (f x) x) f (f (f x))) ∙
        ( ( ap
            ( iterate (length-path-is-finitely-cyclic-map H (f x) x) f)
            ( eq-is-finitely-cyclic-map H (f (f x)) (f x))) ∙
          ( eq-is-finitely-cyclic-map H (f x) x))))

  is-equiv-is-finitely-cyclic-map :
    (f : X → X) → is-finitely-cyclic-map f → is-equiv f
  is-equiv-is-finitely-cyclic-map f H =
    is-equiv-is-invertible
      ( map-inv-is-finitely-cyclic-map f H)
      ( is-section-map-inv-is-finitely-cyclic-map f H)
      ( is-retraction-map-inv-is-finitely-cyclic-map f H)
```

### The successor functions on standard finite types are finitely cyclic

```agda
compute-iterate-succ-Fin :
  {k : ℕ} (n : ℕ) (x : Fin (succ-ℕ k)) →
  iterate n (succ-Fin (succ-ℕ k)) x ＝ add-Fin (succ-ℕ k) x (mod-succ-ℕ k n)
compute-iterate-succ-Fin {k} zero-ℕ x = inv (right-unit-law-add-Fin k x)
compute-iterate-succ-Fin {k} (succ-ℕ n) x =
  ( ap (succ-Fin (succ-ℕ k)) (compute-iterate-succ-Fin n x)) ∙
  ( inv (right-successor-law-add-Fin (succ-ℕ k) x (mod-succ-ℕ k n)))

is-finitely-cyclic-succ-Fin : {k : ℕ} → is-finitely-cyclic-map (succ-Fin k)
pr1 (is-finitely-cyclic-succ-Fin {succ-ℕ k} x y) =
  nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y (neg-Fin (succ-ℕ k) x))
pr2 (is-finitely-cyclic-succ-Fin {succ-ℕ k} x y) =
  ( compute-iterate-succ-Fin
    ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y (neg-Fin (succ-ℕ k) x)))
    ( x)) ∙
    ( ( ap
        ( add-Fin (succ-ℕ k) x)
        ( is-section-nat-Fin k (add-Fin (succ-ℕ k) y (neg-Fin (succ-ℕ k) x)))) ∙
      ( ( commutative-add-Fin
          ( succ-ℕ k)
          ( x)
          ( add-Fin (succ-ℕ k) y (neg-Fin (succ-ℕ k) x))) ∙
        ( ( associative-add-Fin (succ-ℕ k) y (neg-Fin (succ-ℕ k) x) x) ∙
          ( ( ap (add-Fin (succ-ℕ k) y) (left-inverse-law-add-Fin k x)) ∙
            ( right-unit-law-add-Fin k y)))))
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
