# Unbounded π-finite types

```agda
{-# OPTIONS --guardedness #-}

module univalent-combinatorics.unbounded-pi-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-set-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.maybe
open import foundation.mere-equality
open import foundation.mere-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.set-presented-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.finitely-presented-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.truncated-pi-finite-types
```

</details>

## Idea

A type is
{{#concept "unbounded π-finite" Disambiguation="type" Agda=is-unbounded-π-finite Agda=Unbounded-Unbounded-π-Finite-Type}}
if it has [finitely](univalent-combinatorics.finite-types.md) many
[connected components](foundation.connected-components.md) and all of its
homotopy groups at all base points and all dimensions are finite.

## Definitions

### The predicate on types of being unbounded π-finite

```agda
record is-unbounded-π-finite {l : Level} (X : UU l) : UU l
  where
  coinductive
  field
    has-finitely-many-connected-components-is-unbounded-π-finite :
      has-finitely-many-connected-components X

    is-unbounded-π-finite-Id-is-unbounded-π-finite :
      (x y : X) → is-unbounded-π-finite (x ＝ y)

open is-unbounded-π-finite public
```

### The type of unbounded π-finite types

```agda
Unbounded-π-Finite-Type : (l : Level) → UU (lsuc l)
Unbounded-π-Finite-Type l = Σ (UU l) (is-unbounded-π-finite)

module _
  {l : Level} (X : Unbounded-π-Finite-Type l)
  where

  type-Unbounded-π-Finite-Type : UU l
  type-Unbounded-π-Finite-Type = pr1 X

  is-unbounded-π-finite-Unbounded-π-Finite-Type :
    is-unbounded-π-finite type-Unbounded-π-Finite-Type
  is-unbounded-π-finite-Unbounded-π-Finite-Type = pr2 X

  has-finitely-many-connected-components-Unbounded-π-Finite-Type :
    has-finitely-many-connected-components type-Unbounded-π-Finite-Type
  has-finitely-many-connected-components-Unbounded-π-Finite-Type =
    has-finitely-many-connected-components-is-unbounded-π-finite
      ( is-unbounded-π-finite-Unbounded-π-Finite-Type)

  is-unbounded-π-finite-Id-Unbounded-π-Finite-Type :
    (x y : type-Unbounded-π-Finite-Type) → is-unbounded-π-finite (x ＝ y)
  is-unbounded-π-finite-Id-Unbounded-π-Finite-Type =
    is-unbounded-π-finite-Id-is-unbounded-π-finite
      ( is-unbounded-π-finite-Unbounded-π-Finite-Type)
```

## Properties

### Characterizing equality of unbounded π-finiteness

```agda
module _
  {l : Level} {X : UU l}
  where

  Eq-is-unbounded-π-finite :
    (p q : is-unbounded-π-finite X) → UU l
  Eq-is-unbounded-π-finite p q =
    ( has-finitely-many-connected-components-is-unbounded-π-finite p ＝
      has-finitely-many-connected-components-is-unbounded-π-finite q) ×
    ( (x y : X) →
      is-unbounded-π-finite-Id-is-unbounded-π-finite p x y ＝
      is-unbounded-π-finite-Id-is-unbounded-π-finite q x y)

  refl-Eq-is-unbounded-π-finite :
    (p : is-unbounded-π-finite X) → Eq-is-unbounded-π-finite p p
  refl-Eq-is-unbounded-π-finite p = (refl , λ x y → refl)

  Eq-eq-is-unbounded-π-finite :
    (p q : is-unbounded-π-finite X) → p ＝ q → Eq-is-unbounded-π-finite p q
  Eq-eq-is-unbounded-π-finite p .p refl = refl-Eq-is-unbounded-π-finite p
```

### Unbounded π-finite types are closed under equivalences

```agda
is-unbounded-π-finite-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-unbounded-π-finite B → is-unbounded-π-finite A
is-unbounded-π-finite-equiv e H =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    has-finitely-many-connected-components-equiv' e
      ( has-finitely-many-connected-components-is-unbounded-π-finite H)
  .is-unbounded-π-finite-Id-is-unbounded-π-finite x y →
    is-unbounded-π-finite-equiv
      ( equiv-ap e x y)
      ( is-unbounded-π-finite-Id-is-unbounded-π-finite H
        ( map-equiv e x)
        ( map-equiv e y))

is-unbounded-π-finite-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-unbounded-π-finite A → is-unbounded-π-finite B
is-unbounded-π-finite-equiv' e = is-unbounded-π-finite-equiv (inv-equiv e)
```

### Unbounded π-finite types are closed under retracts

```agda
is-unbounded-π-finite-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → is-unbounded-π-finite B → is-unbounded-π-finite A
is-unbounded-π-finite-retract r H =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    has-finitely-many-connected-components-retract r
      ( has-finitely-many-connected-components-is-unbounded-π-finite H)
  .is-unbounded-π-finite-Id-is-unbounded-π-finite x y →
    is-unbounded-π-finite-retract
      ( retract-eq r x y)
      ( is-unbounded-π-finite-Id-is-unbounded-π-finite H
        ( inclusion-retract r x)
        ( inclusion-retract r y))
```

### Empty types are unbounded π-finite

```agda
is-unbounded-π-finite-empty : is-unbounded-π-finite empty
is-unbounded-π-finite-empty =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    has-finitely-many-connected-components-empty
  .is-unbounded-π-finite-Id-is-unbounded-π-finite ()

empty-Unbounded-π-Finite-Type : Unbounded-π-Finite-Type lzero
empty-Unbounded-π-Finite-Type = empty , is-unbounded-π-finite-empty

is-unbounded-π-finite-is-empty :
  {l : Level} {A : UU l} → is-empty A → is-unbounded-π-finite A
is-unbounded-π-finite-is-empty f =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    has-finitely-many-connected-components-is-empty f
  .is-unbounded-π-finite-Id-is-unbounded-π-finite → ex-falso ∘ f
```

### Contractible types are unbounded π-finite

```agda
is-unbounded-π-finite-is-contr :
  {l : Level} {A : UU l} → is-contr A → is-unbounded-π-finite A
is-unbounded-π-finite-is-contr H =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    has-finitely-many-connected-components-is-contr H
  .is-unbounded-π-finite-Id-is-unbounded-π-finite x y →
    is-unbounded-π-finite-is-contr (is-prop-is-contr H x y)

is-unbounded-π-finite-unit : is-unbounded-π-finite unit
is-unbounded-π-finite-unit = is-unbounded-π-finite-is-contr is-contr-unit

unit-Unbounded-π-Finite-Type : Unbounded-π-Finite-Type lzero
unit-Unbounded-π-Finite-Type = unit , is-unbounded-π-finite-unit
```

### Coproducts of π-finite types are π-finite

```agda
is-unbounded-π-finite-coproduct :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-unbounded-π-finite A →
  is-unbounded-π-finite B →
  is-unbounded-π-finite (A + B)
is-unbounded-π-finite-coproduct H K =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    has-finitely-many-connected-components-coproduct
      ( has-finitely-many-connected-components-is-unbounded-π-finite H)
      ( has-finitely-many-connected-components-is-unbounded-π-finite K)
  .is-unbounded-π-finite-Id-is-unbounded-π-finite (inl x) (inl y) →
    is-unbounded-π-finite-equiv
      ( compute-eq-coproduct-inl-inl x y)
      ( is-unbounded-π-finite-Id-is-unbounded-π-finite H x y)
  .is-unbounded-π-finite-Id-is-unbounded-π-finite (inl x) (inr y) →
    is-unbounded-π-finite-equiv
      ( compute-eq-coproduct-inl-inr x y)
      ( is-unbounded-π-finite-empty)
  .is-unbounded-π-finite-Id-is-unbounded-π-finite (inr x) (inl y) →
    is-unbounded-π-finite-equiv
      ( compute-eq-coproduct-inr-inl x y)
      ( is-unbounded-π-finite-empty)
  .is-unbounded-π-finite-Id-is-unbounded-π-finite (inr x) (inr y) →
    is-unbounded-π-finite-equiv
      ( compute-eq-coproduct-inr-inr x y)
      ( is-unbounded-π-finite-Id-is-unbounded-π-finite K x y)

coproduct-Unbounded-π-Finite-Type :
  {l1 l2 : Level} →
  Unbounded-π-Finite-Type l1 →
  Unbounded-π-Finite-Type l2 →
  Unbounded-π-Finite-Type (l1 ⊔ l2)
pr1 (coproduct-Unbounded-π-Finite-Type A B) =
  (type-Unbounded-π-Finite-Type A + type-Unbounded-π-Finite-Type B)
pr2 (coproduct-Unbounded-π-Finite-Type A B) =
  is-unbounded-π-finite-coproduct
    ( is-unbounded-π-finite-Unbounded-π-Finite-Type A)
    ( is-unbounded-π-finite-Unbounded-π-Finite-Type B)
```

### `Maybe A` of any unbounded π-finite type `A` is unbounded π-finite

```agda
Maybe-Unbounded-π-Finite-Type :
  {l : Level} → Unbounded-π-Finite-Type l → Unbounded-π-Finite-Type l
Maybe-Unbounded-π-Finite-Type A =
  coproduct-Unbounded-π-Finite-Type A unit-Unbounded-π-Finite-Type

is-unbounded-π-finite-Maybe :
  {l : Level} {A : UU l} →
  is-unbounded-π-finite A → is-unbounded-π-finite (Maybe A)
is-unbounded-π-finite-Maybe H =
  is-unbounded-π-finite-coproduct H is-unbounded-π-finite-unit
```

### Any stanadard finite type is unbounded π-finite

```agda
is-unbounded-π-finite-Fin :
  (n : ℕ) → is-unbounded-π-finite (Fin n)
is-unbounded-π-finite-Fin zero-ℕ =
  is-unbounded-π-finite-empty
is-unbounded-π-finite-Fin (succ-ℕ n) =
  is-unbounded-π-finite-Maybe (is-unbounded-π-finite-Fin n)

Fin-Unbounded-π-Finite-Type : (n : ℕ) → Unbounded-π-Finite-Type lzero
pr1 (Fin-Unbounded-π-Finite-Type n) = Fin n
pr2 (Fin-Unbounded-π-Finite-Type n) = is-unbounded-π-finite-Fin n
```

### Any type equipped with a counting is unbounded π-finite

```agda
is-unbounded-π-finite-count :
  {l : Level} {A : UU l} → count A → is-unbounded-π-finite A
is-unbounded-π-finite-count (n , e) =
  is-unbounded-π-finite-equiv' e (is-unbounded-π-finite-Fin n)
```

### Any finite type is unbounded π-finite

```agda
is-unbounded-π-finite-is-finite :
  {l : Level} {A : UU l} → is-finite A → is-unbounded-π-finite A
is-unbounded-π-finite-is-finite {A = A} H =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    has-finitely-many-connected-components-is-finite H
  .is-unbounded-π-finite-Id-is-unbounded-π-finite x y →
    is-unbounded-π-finite-is-finite (is-finite-eq-is-finite H)

unbounded-π-finite-𝔽 : {l : Level} → 𝔽 l → Unbounded-π-Finite-Type l
unbounded-π-finite-𝔽 A =
  ( type-𝔽 A , is-unbounded-π-finite-is-finite (is-finite-type-𝔽 A))
```

### The type of all `n`-element types in `UU l` is unbounded π-finite

```agda
is-unbounded-π-finite-UU-Fin :
  {l : Level} (n : ℕ) → is-unbounded-π-finite (UU-Fin l n)
is-unbounded-π-finite-UU-Fin n =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    has-finitely-many-connected-components-UU-Fin n
  .is-unbounded-π-finite-Id-is-unbounded-π-finite x y →
    is-unbounded-π-finite-equiv
      ( equiv-equiv-eq-UU-Fin n x y)
      ( is-unbounded-π-finite-is-finite
        ( is-finite-≃
          ( is-finite-has-finite-cardinality (n , pr2 x))
          ( is-finite-has-finite-cardinality (n , pr2 y))))
```

### Unbounded π-finite sets are finite

```agda
is-finite-is-unbounded-π-finite :
  {l : Level} {A : UU l} → is-set A → is-unbounded-π-finite A → is-finite A
is-finite-is-unbounded-π-finite H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (_ , H))
    ( has-finitely-many-connected-components-is-unbounded-π-finite K)
```

### Truncated π-finite types are unbounded π-finite

```agda
is-unbounded-π-finite-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-truncated-π-finite k A → is-unbounded-π-finite A
is-unbounded-π-finite-is-truncated-π-finite zero-ℕ =
  is-unbounded-π-finite-is-finite
is-unbounded-π-finite-is-truncated-π-finite (succ-ℕ k) H =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    pr1 H
  .is-unbounded-π-finite-Id-is-unbounded-π-finite x y →
    is-unbounded-π-finite-is-truncated-π-finite k (pr2 H x y)
```

### Unbounded π-finite types are types that are πₙ-finite for all `n`

```agda
is-unbounded-π-finite-Id-is-unbounded-π-finite' :
  {l : Level} {A : UU l} →
  ((k : ℕ) → is-π-finite k A) →
  (x y : A) →
  (k : ℕ) → is-π-finite k (x ＝ y)
is-unbounded-π-finite-Id-is-unbounded-π-finite' H x y k = pr2 (H (succ-ℕ k)) x y

is-unbounded-π-finite-is-π-finite :
  {l : Level} {A : UU l} → ((k : ℕ) → is-π-finite k A) → is-unbounded-π-finite A
is-unbounded-π-finite-is-π-finite H =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite → H 0
  .is-unbounded-π-finite-Id-is-unbounded-π-finite x y →
    is-unbounded-π-finite-is-π-finite
      ( is-unbounded-π-finite-Id-is-unbounded-π-finite' H x y)

is-π-finite-is-unbounded-π-finite :
  {l : Level} {A : UU l} → is-unbounded-π-finite A → (k : ℕ) → is-π-finite k A
is-π-finite-is-unbounded-π-finite H zero-ℕ =
  has-finitely-many-connected-components-is-unbounded-π-finite H
pr1 (is-π-finite-is-unbounded-π-finite H (succ-ℕ k)) =
  is-π-finite-is-unbounded-π-finite H zero-ℕ
pr2 (is-π-finite-is-unbounded-π-finite H (succ-ℕ k)) x y =
  is-π-finite-is-unbounded-π-finite
    ( is-unbounded-π-finite-Id-is-unbounded-π-finite H x y)
    ( k)
```

### Finite products of unbounded π-finite types are unbounded π-finite

> Agda is not convinced that the following proof is productive.

```text
is-unbounded-π-finite-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-finite A → ((a : A) → is-unbounded-π-finite (B a)) →
  is-unbounded-π-finite ((a : A) → B a)
is-unbounded-π-finite-Π H K =
  λ where
  .has-finitely-many-connected-components-is-unbounded-π-finite →
    has-finitely-many-connected-components-finite-Π H
      ( λ a →
        has-finitely-many-connected-components-is-unbounded-π-finite (K a))
  .is-unbounded-π-finite-Id-is-unbounded-π-finite f g →
    is-unbounded-π-finite-equiv
      ( equiv-funext)
      ( is-unbounded-π-finite-Π H
        ( λ a →
          is-unbounded-π-finite-Id-is-unbounded-π-finite (K a) (f a) (g a)))
```

Instead, we give a proof using the description of unbounded π-finite types as
types that are πₙ-finite for all n.

```agda
is-unbounded-π-finite-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-finite A → ((a : A) → is-unbounded-π-finite (B a)) →
  is-unbounded-π-finite ((a : A) → B a)
is-unbounded-π-finite-Π H K =
  is-unbounded-π-finite-is-π-finite
    ( λ k →
      is-π-finite-Π k H
        ( λ a → is-π-finite-is-unbounded-π-finite (K a) k))
```

### Dependent sums of unbounded π-finite types

The dependent sum of a family of unbounded π-finite types over an unbounded
π-finite base is unbounded π-finite.

```agda
abstract
  is-unbounded-π-finite-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-unbounded-π-finite A → ((x : A) → is-unbounded-π-finite (B x)) →
    is-unbounded-π-finite (Σ A B)
  is-unbounded-π-finite-Σ H K =
    is-unbounded-π-finite-is-π-finite
      ( λ k →
        is-π-finite-Σ k
          ( is-π-finite-is-unbounded-π-finite H (succ-ℕ k))
          ( λ x → is-π-finite-is-unbounded-π-finite (K x) k))
```

## References

{{#bibliography}} {{#reference Anel24}}

## External links

- [pi-finite type](https://ncatlab.org/nlab/show/pi-finite+type) at $n$Lab
