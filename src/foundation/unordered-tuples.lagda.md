# Unordered `n`-tuples of elements in a type

```agda
module foundation.unordered-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.postcomposition-functions
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.torsorial-type-families

open import univalent-combinatorics.complements-isolated-elements
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An **unordered `n`-tuple** of elements of a type `A` consists of an `n`-element
set `X` equipped with a map `X → A`.

## Definition

```agda
unordered-tuple :
  {l : Level} (n : ℕ) (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-tuple n A = Σ (UU-Fin lzero n) (λ X → type-UU-Fin n X → A)

module _
  {l : Level} (n : ℕ) {A : UU l} (t : unordered-tuple n A)
  where

  type-unordered-tuple-UU-Fin : UU-Fin lzero n
  type-unordered-tuple-UU-Fin = pr1 t

  type-unordered-tuple : UU lzero
  type-unordered-tuple = type-UU-Fin n type-unordered-tuple-UU-Fin

  has-cardinality-type-unordered-tuple : has-cardinality n type-unordered-tuple
  has-cardinality-type-unordered-tuple =
    has-cardinality-type-UU-Fin n type-unordered-tuple-UU-Fin

  is-set-type-unordered-tuple : is-set type-unordered-tuple
  is-set-type-unordered-tuple =
    is-set-has-cardinality n has-cardinality-type-unordered-tuple

  has-decidable-equality-type-unordered-tuple :
    has-decidable-equality type-unordered-tuple
  has-decidable-equality-type-unordered-tuple =
    has-decidable-equality-has-cardinality n
      has-cardinality-type-unordered-tuple

  element-unordered-tuple : type-unordered-tuple → A
  element-unordered-tuple = pr2 t
```

### Unordered tuples away from an index

```agda
module _
  {l : Level} (n : ℕ) {A : UU l} (t : unordered-tuple (succ-ℕ n) A)
  (i : type-unordered-tuple (succ-ℕ n) t)
  where

  type-complement-point-unordered-tuple-UU-Fin : UU-Fin lzero n
  type-complement-point-unordered-tuple-UU-Fin =
    complement-element-UU-Fin n
      ( pair (type-unordered-tuple-UU-Fin (succ-ℕ n) t) i)

  type-complement-point-unordered-tuple : UU lzero
  type-complement-point-unordered-tuple =
    type-UU-Fin n type-complement-point-unordered-tuple-UU-Fin

  inclusion-complement-point-unordered-tuple :
    type-complement-point-unordered-tuple → type-unordered-tuple (succ-ℕ n) t
  inclusion-complement-point-unordered-tuple =
    inclusion-complement-element-UU-Fin n
      ( pair (type-unordered-tuple-UU-Fin (succ-ℕ n) t) i)

  unordered-tuple-complement-point-type-unordered-tuple :
    unordered-tuple n A
  pr1 unordered-tuple-complement-point-type-unordered-tuple =
    complement-element-UU-Fin n
      ( pair (type-unordered-tuple-UU-Fin (succ-ℕ n) t) i)
  pr2 unordered-tuple-complement-point-type-unordered-tuple =
    ( element-unordered-tuple (succ-ℕ n) t) ∘
    ( inclusion-complement-point-unordered-tuple)
```

### Standard unordered tuples

```agda
standard-unordered-tuple :
  {l : Level} (n : ℕ) {A : UU l} (f : Fin n → A) → unordered-tuple n A
pr1 (standard-unordered-tuple n f) = Fin-UU-Fin' n
pr2 (standard-unordered-tuple n f) = f
```

## Properties

### Equality of unordered tuples

```agda
module _
  {l : Level} (n : ℕ) {A : UU l}
  where

  Eq-unordered-tuple : unordered-tuple n A → unordered-tuple n A → UU l
  Eq-unordered-tuple x y =
    Σ ( type-unordered-tuple n x ≃ type-unordered-tuple n y)
      ( λ e →
        ( element-unordered-tuple n x) ~
        ( element-unordered-tuple n y ∘ map-equiv e))

  refl-Eq-unordered-tuple :
    (x : unordered-tuple n A) → Eq-unordered-tuple x x
  pr1 (refl-Eq-unordered-tuple x) = id-equiv
  pr2 (refl-Eq-unordered-tuple x) = refl-htpy

  Eq-eq-unordered-tuple :
    (x y : unordered-tuple n A) → x ＝ y → Eq-unordered-tuple x y
  Eq-eq-unordered-tuple x .x refl = refl-Eq-unordered-tuple x

  is-torsorial-Eq-unordered-tuple :
    (x : unordered-tuple n A) → is-torsorial (Eq-unordered-tuple x)
  is-torsorial-Eq-unordered-tuple x =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-UU-Fin {k = n} (type-unordered-tuple-UU-Fin n x))
      ( pair (type-unordered-tuple-UU-Fin n x) id-equiv)
      ( is-torsorial-htpy (element-unordered-tuple n x))

  is-equiv-Eq-eq-unordered-tuple :
    (x y : unordered-tuple n A) → is-equiv (Eq-eq-unordered-tuple x y)
  is-equiv-Eq-eq-unordered-tuple x =
    fundamental-theorem-id
      ( is-torsorial-Eq-unordered-tuple x)
      ( Eq-eq-unordered-tuple x)

  extensionality-unordered-tuple :
    (x y : unordered-tuple n A) → (x ＝ y) ≃ Eq-unordered-tuple x y
  pr1 (extensionality-unordered-tuple x y) = Eq-eq-unordered-tuple x y
  pr2 (extensionality-unordered-tuple x y) = is-equiv-Eq-eq-unordered-tuple x y

  eq-Eq-unordered-tuple :
    (x y : unordered-tuple n A) → Eq-unordered-tuple x y → x ＝ y
  eq-Eq-unordered-tuple x y =
    map-inv-is-equiv (is-equiv-Eq-eq-unordered-tuple x y)

  is-retraction-eq-Eq-unordered-tuple :
    (x y : unordered-tuple n A) →
    (eq-Eq-unordered-tuple x y ∘ Eq-eq-unordered-tuple x y) ~ id
  is-retraction-eq-Eq-unordered-tuple x y =
    is-retraction-map-inv-is-equiv (is-equiv-Eq-eq-unordered-tuple x y)
```

### Functoriality of unordered tuples

```agda
map-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} (f : A → B) →
  unordered-tuple n A → unordered-tuple n B
pr1 (map-unordered-tuple n f t) = type-unordered-tuple-UU-Fin n t
pr2 (map-unordered-tuple n f t) = f ∘ element-unordered-tuple n t

preserves-comp-map-unordered-tuple :
  {l1 l2 l3 : Level} (n : ℕ) {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-unordered-tuple n (g ∘ f) ~
  (map-unordered-tuple n g ∘ map-unordered-tuple n f)
preserves-comp-map-unordered-tuple n g f p = refl

preserves-id-map-unordered-tuple :
  {l1 : Level} (n : ℕ) {A : UU l1} →
  map-unordered-tuple n (id {A = A}) ~ id
preserves-id-map-unordered-tuple n = refl-htpy

htpy-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → (map-unordered-tuple n f ~ map-unordered-tuple n g)
htpy-unordered-tuple n {f = f} {g = g} H t =
  eq-Eq-unordered-tuple n
    ( map-unordered-tuple n f t)
    ( map-unordered-tuple n g t)
    ( pair id-equiv (H ·r element-unordered-tuple n t))

preserves-refl-htpy-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} (f : A → B) →
  htpy-unordered-tuple n (refl-htpy {f = f}) ~ refl-htpy
preserves-refl-htpy-unordered-tuple n f p =
  is-retraction-eq-Eq-unordered-tuple n
    ( map-unordered-tuple n f p)
    ( map-unordered-tuple n f p)
    ( refl)

equiv-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-tuple n A ≃ unordered-tuple n B)
equiv-unordered-tuple n e = equiv-tot (λ X → equiv-postcomp (type-UU-Fin n X) e)

map-equiv-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-tuple n A → unordered-tuple n B)
map-equiv-unordered-tuple n e = map-equiv (equiv-unordered-tuple n e)

is-equiv-map-equiv-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-equiv (map-equiv-unordered-tuple n e)
is-equiv-map-equiv-unordered-tuple n e =
  is-equiv-map-equiv (equiv-unordered-tuple n e)
```
