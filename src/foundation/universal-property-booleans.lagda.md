# The universal property of booleans

```agda
module foundation.universal-property-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

```agda
ev-true-false :
  {l : Level} (A : UU l) → (f : bool → A) → A × A
ev-true-false A f = pair (f true) (f false)

map-universal-property-bool :
  {l : Level} {A : UU l} →
  A × A → (bool → A)
map-universal-property-bool (pair x y) true = x
map-universal-property-bool (pair x y) false = y

abstract
  is-section-map-universal-property-bool :
    {l : Level} {A : UU l} →
    is-section (ev-true-false A) (map-universal-property-bool)
  is-section-map-universal-property-bool (pair x y) = refl

abstract
  is-retraction-map-universal-property-bool' :
    {l : Level} {A : UU l} (f : bool → A) →
    (map-universal-property-bool (ev-true-false A f)) ~ f
  is-retraction-map-universal-property-bool' f true = refl
  is-retraction-map-universal-property-bool' f false = refl

abstract
  is-retraction-map-universal-property-bool :
    {l : Level} {A : UU l} →
    is-retraction (ev-true-false A) (map-universal-property-bool)
  is-retraction-map-universal-property-bool f =
    eq-htpy (is-retraction-map-universal-property-bool' f)

abstract
  universal-property-bool :
    {l : Level} (A : UU l) →
    is-equiv (λ (f : bool → A) → (f true , f false))
  universal-property-bool A =
    is-equiv-is-invertible
      map-universal-property-bool
      is-section-map-universal-property-bool
      is-retraction-map-universal-property-bool

ev-true :
  {l : Level} {A : UU l} → (bool → A) → A
ev-true f = f true

triangle-ev-true :
  {l : Level} (A : UU l) →
  ev-true ~ pr1 ∘ ev-true-false A
triangle-ev-true A = refl-htpy

{-
aut-bool-bool :
  bool → (bool ≃ bool)
aut-bool-bool true = id-equiv
aut-bool-bool false = equiv-neg-bool

bool-aut-bool :
  (bool ≃ bool) → bool
bool-aut-bool e = map-equiv e true

decide-true-false :
  (b : bool) → coproduct (b ＝ true) (b ＝ false)
decide-true-false true = inl refl
decide-true-false false = inr refl

eq-false :
  (b : bool) → (b ≠ true) → (b ＝ false)
eq-false true p = ind-empty (p refl)
eq-false false p = refl

eq-true :
  (b : bool) → b ≠ false → b ＝ true
eq-true true p = refl
eq-true false p = ind-empty (p refl)

Eq-eq-bool : (x y : bool) → x ＝ y → Eq-bool x y
Eq-eq-bool x .x refl = reflexive-Eq-bool x

eq-false-equiv' :
  (e : bool ≃ bool) → map-equiv e true ＝ true →
  is-decidable (map-equiv e false ＝ false) → map-equiv e false ＝ false
eq-false-equiv' e p (inl q) = q
eq-false-equiv' e p (inr x) =
  ind-empty
    ( Eq-eq-bool true false
      ( ap pr1
        ( eq-is-contr'
          ( is-contr-map-is-equiv (is-equiv-map-equiv e) true)
          ( pair true p)
          ( pair false (eq-true (map-equiv e false) x)))))
-}
```

### The canonical projection from a coproduct to the booleans

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  projection-bool-coproduct : A + B → bool
  projection-bool-coproduct (inl _) = true
  projection-bool-coproduct (inr _) = false
```
