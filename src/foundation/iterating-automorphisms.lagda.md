# Iterating automorphisms

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.iterating-automorphisms
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers funext univalence truncations
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.automorphisms funext univalence
open import foundation.equivalence-extensionality funext
open import foundation.iterating-functions funext univalence truncations
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Definition

### Iterating automorphisms

#### Iterating by postcomposition using a natural number

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-ℕ : ℕ → Aut X → Aut X
  iterate-automorphism-ℕ zero-ℕ e = id-equiv
  iterate-automorphism-ℕ (succ-ℕ n) e = e ∘e (iterate-automorphism-ℕ n e)

  map-iterate-automorphism : ℕ → Aut X → X → X
  map-iterate-automorphism n e = map-equiv (iterate-automorphism-ℕ n e)

  is-equiv-map-iterate-automorphism :
    (n : ℕ) (e : Aut X) → is-equiv (map-iterate-automorphism n e)
  is-equiv-map-iterate-automorphism n e =
    is-equiv-map-equiv (iterate-automorphism-ℕ n e)

  compute-map-iterate-automorphism :
    (n : ℕ) (e : Aut X) → map-iterate-automorphism n e ~ iterate n (map-equiv e)
  compute-map-iterate-automorphism zero-ℕ e = refl-htpy
  compute-map-iterate-automorphism (succ-ℕ n) e =
    map-equiv e ·l (compute-map-iterate-automorphism n e)
```

#### Iterating by precomposition using a natural number

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-ℕ' : ℕ → Aut X → Aut X
  iterate-automorphism-ℕ' zero-ℕ e = id-equiv
  iterate-automorphism-ℕ' (succ-ℕ n) e = iterate-automorphism-ℕ' n e ∘e e

  map-iterate-automorphism-ℕ' : ℕ → Aut X → X → X
  map-iterate-automorphism-ℕ' n e = map-equiv (iterate-automorphism-ℕ' n e)

  is-equiv-map-iterate-automorphism-ℕ' :
    (n : ℕ) (e : Aut X) → is-equiv (map-iterate-automorphism-ℕ' n e)
  is-equiv-map-iterate-automorphism-ℕ' n e =
    is-equiv-map-equiv (iterate-automorphism-ℕ' n e)

  compute-map-iterate-automorphism-ℕ' :
    (n : ℕ) (e : Aut X) →
    map-iterate-automorphism-ℕ' n e ~ iterate' n (map-equiv e)
  compute-map-iterate-automorphism-ℕ' zero-ℕ e = refl-htpy
  compute-map-iterate-automorphism-ℕ' (succ-ℕ n) e =
    (compute-map-iterate-automorphism-ℕ' n e ·r (map-equiv e))
```

#### Iterating by postcomposition using an integer

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-ℤ : ℤ → Aut X → Aut X
  iterate-automorphism-ℤ (inl zero-ℕ) e = inv-equiv e
  iterate-automorphism-ℤ (inl (succ-ℕ x)) e =
    inv-equiv e ∘e (iterate-automorphism-ℤ (inl x) e)
  iterate-automorphism-ℤ (inr (inl _)) e = id-equiv
  iterate-automorphism-ℤ (inr (inr zero-ℕ)) e = e
  iterate-automorphism-ℤ (inr (inr (succ-ℕ x))) e =
    e ∘e (iterate-automorphism-ℤ (inr (inr x)) e)

  map-iterate-automorphism-ℤ : ℤ → Aut X → X → X
  map-iterate-automorphism-ℤ k e = map-equiv (iterate-automorphism-ℤ k e)

  is-equiv-map-iterate-automorphism-ℤ :
    (k : ℤ) (e : Aut X) → is-equiv (map-iterate-automorphism-ℤ k e)
  is-equiv-map-iterate-automorphism-ℤ k e =
    is-equiv-map-equiv (iterate-automorphism-ℤ k e)

  map-inv-iterate-automorphism-ℤ : ℤ → Aut X → X → X
  map-inv-iterate-automorphism-ℤ k e =
    map-inv-equiv (iterate-automorphism-ℤ k e)

  is-section-map-inv-iterate-automorphism-ℤ :
    (k : ℤ) (e : Aut X) →
    (map-iterate-automorphism-ℤ k e ∘ map-inv-iterate-automorphism-ℤ k e) ~ id
  is-section-map-inv-iterate-automorphism-ℤ k e =
    is-section-map-inv-equiv (iterate-automorphism-ℤ k e)

  is-retraction-map-inv-iterate-automorphism-ℤ :
    (k : ℤ) (e : Aut X) →
    (map-inv-iterate-automorphism-ℤ k e ∘ map-iterate-automorphism-ℤ k e) ~ id
  is-retraction-map-inv-iterate-automorphism-ℤ k e =
    is-retraction-map-inv-equiv (iterate-automorphism-ℤ k e)
```

#### Iterating by precomposition using an integer

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-ℤ' : ℤ → Aut X → Aut X
  iterate-automorphism-ℤ' (inl zero-ℕ) e = inv-equiv e
  iterate-automorphism-ℤ' (inl (succ-ℕ x)) e =
    iterate-automorphism-ℤ' (inl x) e ∘e inv-equiv e
  iterate-automorphism-ℤ' (inr (inl _)) e = id-equiv
  iterate-automorphism-ℤ' (inr (inr zero-ℕ)) e = e
  iterate-automorphism-ℤ' (inr (inr (succ-ℕ x))) e =
    iterate-automorphism-ℤ' (inr (inr x)) e ∘e e
```

## Properties

### Iterating an automorphism by a natural number `n` is the same as iterating it by the integer `int-ℕ n`

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-int-ℕ :
    (n : ℕ) (e : Aut X) →
    htpy-equiv (iterate-automorphism-ℕ n e) (iterate-automorphism-ℤ (int-ℕ n) e)
  iterate-automorphism-int-ℕ zero-ℕ e = refl-htpy
  iterate-automorphism-int-ℕ (succ-ℕ zero-ℕ) e = refl-htpy
  iterate-automorphism-int-ℕ (succ-ℕ (succ-ℕ n)) e =
    map-equiv e ·l (iterate-automorphism-int-ℕ (succ-ℕ n) e)
```

### Iterating by postcomposition is homotopic to iterating by precomposition

#### For the natural numbers

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-succ-ℕ :
    (n : ℕ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℕ (succ-ℕ n) e)
      ( iterate-automorphism-ℕ n e ∘e e)
  iterate-automorphism-succ-ℕ zero-ℕ e = refl-htpy
  iterate-automorphism-succ-ℕ (succ-ℕ n) e =
    map-equiv e ·l (iterate-automorphism-succ-ℕ n e)

  reassociate-iterate-automorphism-ℕ :
    (n : ℕ) (e : Aut X) →
    htpy-equiv (iterate-automorphism-ℕ n e) (iterate-automorphism-ℕ' n e)
  reassociate-iterate-automorphism-ℕ zero-ℕ e = refl-htpy
  reassociate-iterate-automorphism-ℕ (succ-ℕ n) e =
    ( iterate-automorphism-succ-ℕ n e) ∙h
    ( reassociate-iterate-automorphism-ℕ n e ·r map-equiv e)
```

#### For the integers

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-succ-ℤ :
    (k : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (succ-ℤ k) e)
      ( iterate-automorphism-ℤ k e ∘e e)
  iterate-automorphism-succ-ℤ (inl zero-ℕ) e =
    inv-htpy (is-retraction-map-inv-equiv e)
  iterate-automorphism-succ-ℤ (inl (succ-ℕ zero-ℕ)) e =
    inv-htpy (map-inv-equiv e ·l is-retraction-map-inv-equiv e)
  iterate-automorphism-succ-ℤ (inl (succ-ℕ (succ-ℕ x))) e =
    map-inv-equiv e ·l iterate-automorphism-succ-ℤ (inl (succ-ℕ x)) e
  iterate-automorphism-succ-ℤ (inr (inl _)) e = refl-htpy
  iterate-automorphism-succ-ℤ (inr (inr zero-ℕ)) e = refl-htpy
  iterate-automorphism-succ-ℤ (inr (inr (succ-ℕ x))) e =
    map-equiv e ·l iterate-automorphism-succ-ℤ (inr (inr x)) e

  iterate-automorphism-succ-ℤ' :
    (k : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (succ-ℤ k) e)
      ( e ∘e iterate-automorphism-ℤ k e)
  iterate-automorphism-succ-ℤ' (inl zero-ℕ) e =
    inv-htpy (is-section-map-inv-equiv e)
  iterate-automorphism-succ-ℤ' (inl (succ-ℕ x)) e =
    ( inv-htpy (is-section-map-inv-equiv e)) ·r
    ( map-iterate-automorphism-ℤ (inl x) e)
  iterate-automorphism-succ-ℤ' (inr (inl _)) e = refl-htpy
  iterate-automorphism-succ-ℤ' (inr (inr x)) e = refl-htpy

  iterate-automorphism-pred-ℤ :
    (k : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (pred-ℤ k) e)
      ( iterate-automorphism-ℤ k e ∘e inv-equiv e)
  iterate-automorphism-pred-ℤ (inl zero-ℕ) e = refl-htpy
  iterate-automorphism-pred-ℤ (inl (succ-ℕ x)) e =
    map-inv-equiv e ·l iterate-automorphism-pred-ℤ (inl x) e
  iterate-automorphism-pred-ℤ (inr (inl _)) e = refl-htpy
  iterate-automorphism-pred-ℤ (inr (inr zero-ℕ)) e =
    inv-htpy (is-section-map-inv-equiv e)
  iterate-automorphism-pred-ℤ (inr (inr (succ-ℕ zero-ℕ))) e =
    inv-htpy (map-equiv e ·l is-section-map-inv-equiv e)
  iterate-automorphism-pred-ℤ (inr (inr (succ-ℕ (succ-ℕ x)))) e =
    map-equiv e ·l iterate-automorphism-pred-ℤ (inr (inr (succ-ℕ x))) e

  iterate-automorphism-pred-ℤ' :
    (k : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (pred-ℤ k) e)
      ( inv-equiv e ∘e iterate-automorphism-ℤ k e)
  iterate-automorphism-pred-ℤ' (inl zero-ℕ) e = refl-htpy
  iterate-automorphism-pred-ℤ' (inl (succ-ℕ x)) e = refl-htpy
  iterate-automorphism-pred-ℤ' (inr (inl _)) e = refl-htpy
  iterate-automorphism-pred-ℤ' (inr (inr zero-ℕ)) e =
    inv-htpy (is-retraction-map-inv-equiv e)
  iterate-automorphism-pred-ℤ' (inr (inr (succ-ℕ x))) e =
    ( inv-htpy (is-retraction-map-inv-equiv e)) ·r
    ( map-equiv (iterate-automorphism-ℤ (inr (inr x)) e))

  reassociate-iterate-automorphism-ℤ :
    (k : ℤ) (e : Aut X) →
    htpy-equiv (iterate-automorphism-ℤ k e) (iterate-automorphism-ℤ' k e)
  reassociate-iterate-automorphism-ℤ (inl zero-ℕ) e = refl-htpy
  reassociate-iterate-automorphism-ℤ (inl (succ-ℕ x)) e =
    ( iterate-automorphism-pred-ℤ (inl x) e) ∙h
    ( reassociate-iterate-automorphism-ℤ (inl x) e ·r map-inv-equiv e)
  reassociate-iterate-automorphism-ℤ (inr (inl _)) e = refl-htpy
  reassociate-iterate-automorphism-ℤ (inr (inr zero-ℕ)) e = refl-htpy
  reassociate-iterate-automorphism-ℤ (inr (inr (succ-ℕ x))) e =
    ( iterate-automorphism-succ-ℤ (inr (inr x)) e) ∙h
    ( reassociate-iterate-automorphism-ℤ (inr (inr x)) e ·r map-equiv e)
```

### Iterating an automorphism `k+l` times

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-add-ℤ :
    (k l : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (k +ℤ l) e)
      ( iterate-automorphism-ℤ k e ∘e iterate-automorphism-ℤ l e)
  iterate-automorphism-add-ℤ (inl zero-ℕ) l e = iterate-automorphism-pred-ℤ' l e
  iterate-automorphism-add-ℤ (inl (succ-ℕ k)) l e =
    ( iterate-automorphism-pred-ℤ' ((inl k) +ℤ l) e) ∙h
    ( map-inv-equiv e ·l iterate-automorphism-add-ℤ (inl k) l e)
  iterate-automorphism-add-ℤ (inr (inl _)) l e = refl-htpy
  iterate-automorphism-add-ℤ (inr (inr zero-ℕ)) l e =
    iterate-automorphism-succ-ℤ' l e
  iterate-automorphism-add-ℤ (inr (inr (succ-ℕ x))) l e =
    ( iterate-automorphism-succ-ℤ' ((inr (inr x)) +ℤ l) e) ∙h
    ( map-equiv e ·l iterate-automorphism-add-ℤ (inr (inr x)) l e)
```
