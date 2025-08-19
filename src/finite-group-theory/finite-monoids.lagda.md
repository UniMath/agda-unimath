# Finite monoids

```agda
module finite-group-theory.finite-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-semigroups

open import foundation.1-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.truncated-pi-finite-types
open import univalent-combinatorics.untruncated-pi-finite-types
```

</details>

## Idea

A {{#concept "finite monoid" Agda=Finite-Monoid}} is a
[monoid](group-theory.monoids.md) of which the underlying type is
[finite](univalent-combinatorics.finite-types.md).

## Definition

### The type of finite monoids

```agda
is-unital-Finite-Semigroup :
  {l : Level} → Finite-Semigroup l → UU l
is-unital-Finite-Semigroup G = is-unital (mul-Finite-Semigroup G)

Finite-Monoid :
  (l : Level) → UU (lsuc l)
Finite-Monoid l = Σ (Finite-Semigroup l) is-unital-Finite-Semigroup

module _
  {l : Level} (M : Finite-Monoid l)
  where

  finite-semigroup-Finite-Monoid : Finite-Semigroup l
  finite-semigroup-Finite-Monoid = pr1 M

  semigroup-Finite-Monoid : Semigroup l
  semigroup-Finite-Monoid =
    semigroup-Finite-Semigroup finite-semigroup-Finite-Monoid

  finite-type-Finite-Monoid : Finite-Type l
  finite-type-Finite-Monoid =
    finite-type-Finite-Semigroup finite-semigroup-Finite-Monoid

  type-Finite-Monoid : UU l
  type-Finite-Monoid = type-Finite-Semigroup finite-semigroup-Finite-Monoid

  is-finite-type-Finite-Monoid : is-finite type-Finite-Monoid
  is-finite-type-Finite-Monoid =
    is-finite-type-Finite-Semigroup finite-semigroup-Finite-Monoid

  set-Finite-Monoid : Set l
  set-Finite-Monoid = set-Semigroup semigroup-Finite-Monoid

  is-set-type-Finite-Monoid : is-set type-Finite-Monoid
  is-set-type-Finite-Monoid = is-set-type-Semigroup semigroup-Finite-Monoid

  mul-Finite-Monoid :
    type-Finite-Monoid → type-Finite-Monoid → type-Finite-Monoid
  mul-Finite-Monoid = mul-Semigroup semigroup-Finite-Monoid

  mul-Finite-Monoid' :
    type-Finite-Monoid → type-Finite-Monoid → type-Finite-Monoid
  mul-Finite-Monoid' y x = mul-Finite-Monoid x y

  ap-mul-Finite-Monoid :
    {x x' y y' : type-Finite-Monoid} →
    x ＝ x' → y ＝ y' → mul-Finite-Monoid x y ＝ mul-Finite-Monoid x' y'
  ap-mul-Finite-Monoid = ap-mul-Semigroup semigroup-Finite-Monoid

  associative-mul-Finite-Monoid :
    (x y z : type-Finite-Monoid) →
    mul-Finite-Monoid (mul-Finite-Monoid x y) z ＝
    mul-Finite-Monoid x (mul-Finite-Monoid y z)
  associative-mul-Finite-Monoid =
    associative-mul-Semigroup semigroup-Finite-Monoid

  has-unit-Finite-Monoid : is-unital mul-Finite-Monoid
  has-unit-Finite-Monoid = pr2 M

  monoid-Finite-Monoid : Monoid l
  pr1 monoid-Finite-Monoid = semigroup-Finite-Monoid
  pr2 monoid-Finite-Monoid = has-unit-Finite-Monoid

  unit-Finite-Monoid : type-Finite-Monoid
  unit-Finite-Monoid = unit-Monoid monoid-Finite-Monoid

  left-unit-law-mul-Finite-Monoid :
    (x : type-Finite-Monoid) → mul-Finite-Monoid unit-Finite-Monoid x ＝ x
  left-unit-law-mul-Finite-Monoid =
    left-unit-law-mul-Monoid monoid-Finite-Monoid

  right-unit-law-mul-Finite-Monoid :
    (x : type-Finite-Monoid) → mul-Finite-Monoid x unit-Finite-Monoid ＝ x
  right-unit-law-mul-Finite-Monoid =
    right-unit-law-mul-Monoid monoid-Finite-Monoid
```

### Monoids of order `n`

```agda
Monoid-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Monoid-of-Order l n = Σ (Monoid l) (λ M → mere-equiv (Fin n) (type-Monoid M))

Monoid-of-Order' : (l : Level) (n : ℕ) → UU (lsuc l)
Monoid-of-Order' l n =
    Σ (Semigroup-of-Order l n) (λ X → is-unital-Semigroup (pr1 X))

compute-Monoid-of-Order :
  {l : Level} (n : ℕ) → Monoid-of-Order l n ≃ Monoid-of-Order' l n
compute-Monoid-of-Order n = equiv-right-swap-Σ
```

## Properties

### For any semigroup of order `n`, the type of multiplicative units is finite

```agda
is-finite-is-unital-Semigroup :
  {l : Level} (n : ℕ) (X : Semigroup-of-Order l n) →
  is-finite (is-unital-Semigroup (pr1 X))
is-finite-is-unital-Semigroup {l} n X =
  apply-universal-property-trunc-Prop
    ( pr2 X)
    ( is-finite-Prop _)
    ( λ e →
      is-finite-is-decidable-Prop
        ( is-unital-prop-Semigroup (pr1 X))
        ( is-decidable-Σ-count
          ( pair n e)
          ( λ u →
            is-decidable-product
              ( is-decidable-Π-count
                ( pair n e)
                ( λ x →
                  has-decidable-equality-count
                    ( pair n e)
                    ( mul-Semigroup (pr1 X) u x)
                    ( x)))
              ( is-decidable-Π-count
                ( pair n e)
                ( λ x →
                  has-decidable-equality-count
                    ( pair n e)
                    ( mul-Semigroup (pr1 X) x u)
                    ( x))))))
```

### The type of monoids of order `n` is a 1-type

```agda
is-1-type-Monoid-of-Order' :
  {l : Level} (n : ℕ) → is-1-type (Monoid-of-Order' l n)
is-1-type-Monoid-of-Order' n =
  is-1-type-Σ
    ( is-1-type-Semigroup-of-Order n)
    ( λ G →
      is-1-type-is-set (is-set-is-finite (is-finite-is-unital-Semigroup n G)))

is-1-type-Monoid-of-Order :
  {l : Level} (n : ℕ) → is-1-type (Monoid-of-Order l n)
is-1-type-Monoid-of-Order {l} n =
  is-1-type-equiv
    ( Monoid-of-Order' l n)
    ( compute-Monoid-of-Order n)
    ( is-1-type-Monoid-of-Order' n)
```

### The type of monoids of order `n` is π₁-finite

```agda
is-untruncated-π-finite-Monoid-of-Order :
  {l : Level} (k n : ℕ) → is-untruncated-π-finite k (Monoid-of-Order l n)
is-untruncated-π-finite-Monoid-of-Order {l} k n =
  is-untruncated-π-finite-equiv k
    ( compute-Monoid-of-Order n)
    ( is-untruncated-π-finite-Σ k
      ( is-untruncated-π-finite-Semigroup-of-Order (succ-ℕ k) n)
      ( λ X →
        is-untruncated-π-finite-is-finite k
          ( is-finite-is-unital-Semigroup n X)))

is-truncated-π-finite-Monoid-of-Order :
  {l : Level} (n : ℕ) → is-truncated-π-finite 1 (Monoid-of-Order l n)
is-truncated-π-finite-Monoid-of-Order n =
  is-truncated-π-finite-is-untruncated-π-finite 1
    ( is-1-type-Monoid-of-Order n)
    ( is-untruncated-π-finite-Monoid-of-Order 1 n)
```

### The number of monoids of a given order up to isomorphism

The number of monoids of order `n` is listed as
[A058129](https://oeis.org/A058129) in the [OEIS](literature.oeis.md)
{{#cite oeis}}.

```agda
number-of-monoids-of-order : ℕ → ℕ
number-of-monoids-of-order n =
  number-of-connected-components
    ( is-untruncated-π-finite-Monoid-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-monoids-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-monoids-of-order n))
    ( type-trunc-Set (Monoid-of-Order lzero n))
mere-equiv-number-of-monoids-of-order n =
  mere-equiv-number-of-connected-components
    ( is-untruncated-π-finite-Monoid-of-Order {lzero} zero-ℕ n)
```

### For any finite semigroup `G`, being unital is a property

```agda
abstract
  is-prop-is-unital-Finite-Semigroup :
    {l : Level} (G : Finite-Semigroup l) →
    is-prop (is-unital-Finite-Semigroup G)
  is-prop-is-unital-Finite-Semigroup G =
    is-prop-is-unital-Semigroup (semigroup-Finite-Semigroup G)

is-unital-Finite-Semigroup-Prop : {l : Level} (G : Finite-Semigroup l) → Prop l
pr1 (is-unital-Finite-Semigroup-Prop G) = is-unital-Finite-Semigroup G
pr2 (is-unital-Finite-Semigroup-Prop G) = is-prop-is-unital-Finite-Semigroup G
```

### For any finite semigroup `G`, being unital is finite

```agda
is-finite-is-unital-Finite-Semigroup :
  {l : Level} (G : Finite-Semigroup l) →
  is-finite (is-unital-Finite-Semigroup G)
is-finite-is-unital-Finite-Semigroup G =
  is-finite-Σ
    ( is-finite-type-Finite-Semigroup G)
    ( λ e →
      is-finite-product
        ( is-finite-Π
          ( is-finite-type-Finite-Semigroup G)
          ( λ x → is-finite-eq-Finite-Type (finite-type-Finite-Semigroup G)))
        ( is-finite-Π
          ( is-finite-type-Finite-Semigroup G)
          ( λ x → is-finite-eq-Finite-Type (finite-type-Finite-Semigroup G))))
```

### There is a finite number of ways to equip a finite type with the structure of a monoid

```agda
structure-monoid-Finite-Type :
  {l1 : Level} → Finite-Type l1 → UU l1
structure-monoid-Finite-Type X =
  Σ ( structure-semigroup-Finite-Type X)
    ( λ p → is-unital-Finite-Semigroup (X , p))

finite-monoid-structure-monoid-Finite-Type :
  {l : Level} → (X : Finite-Type l) →
  structure-monoid-Finite-Type X → Finite-Monoid l
pr1 (finite-monoid-structure-monoid-Finite-Type X (a , u)) = X , a
pr2 (finite-monoid-structure-monoid-Finite-Type X (a , u)) = u

is-finite-structure-monoid-Finite-Type :
  {l : Level} → (X : Finite-Type l) → is-finite (structure-monoid-Finite-Type X)
is-finite-structure-monoid-Finite-Type X =
  is-finite-Σ
    ( is-finite-structure-semigroup-Finite-Type X)
    ( λ m → is-finite-is-unital-Finite-Semigroup (X , m))
```

## References

{{#bibliography}}
