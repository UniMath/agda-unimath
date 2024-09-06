# Finite monoids

```agda
module finite-group-theory.finite-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-semigroups

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
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A finite monoid is a monoid of which the underlying type is finite.

## Definition

### The type of finite monoids

```agda
is-unital-Semigroup-𝔽 :
  {l : Level} → Semigroup-𝔽 l → UU l
is-unital-Semigroup-𝔽 G = is-unital (mul-Semigroup-𝔽 G)

Monoid-𝔽 :
  (l : Level) → UU (lsuc l)
Monoid-𝔽 l = Σ (Semigroup-𝔽 l) is-unital-Semigroup-𝔽

module _
  {l : Level} (M : Monoid-𝔽 l)
  where

  finite-semigroup-Monoid-𝔽 : Semigroup-𝔽 l
  finite-semigroup-Monoid-𝔽 = pr1 M

  semigroup-Monoid-𝔽 : Semigroup l
  semigroup-Monoid-𝔽 = semigroup-Semigroup-𝔽 finite-semigroup-Monoid-𝔽

  finite-type-Monoid-𝔽 : 𝔽 l
  finite-type-Monoid-𝔽 = finite-type-Semigroup-𝔽 finite-semigroup-Monoid-𝔽

  type-Monoid-𝔽 : UU l
  type-Monoid-𝔽 = type-Semigroup-𝔽 finite-semigroup-Monoid-𝔽

  is-finite-type-Monoid-𝔽 : is-finite type-Monoid-𝔽
  is-finite-type-Monoid-𝔽 = is-finite-type-Semigroup-𝔽 finite-semigroup-Monoid-𝔽

  set-Monoid-𝔽 : Set l
  set-Monoid-𝔽 = set-Semigroup semigroup-Monoid-𝔽

  is-set-type-Monoid-𝔽 : is-set type-Monoid-𝔽
  is-set-type-Monoid-𝔽 = is-set-type-Semigroup semigroup-Monoid-𝔽

  mul-Monoid-𝔽 : type-Monoid-𝔽 → type-Monoid-𝔽 → type-Monoid-𝔽
  mul-Monoid-𝔽 = mul-Semigroup semigroup-Monoid-𝔽

  mul-Monoid-𝔽' : type-Monoid-𝔽 → type-Monoid-𝔽 → type-Monoid-𝔽
  mul-Monoid-𝔽' y x = mul-Monoid-𝔽 x y

  ap-mul-Monoid-𝔽 :
    {x x' y y' : type-Monoid-𝔽} →
    x ＝ x' → y ＝ y' → mul-Monoid-𝔽 x y ＝ mul-Monoid-𝔽 x' y'
  ap-mul-Monoid-𝔽 = ap-mul-Semigroup semigroup-Monoid-𝔽

  associative-mul-Monoid-𝔽 :
    (x y z : type-Monoid-𝔽) →
    mul-Monoid-𝔽 (mul-Monoid-𝔽 x y) z ＝ mul-Monoid-𝔽 x (mul-Monoid-𝔽 y z)
  associative-mul-Monoid-𝔽 = associative-mul-Semigroup semigroup-Monoid-𝔽

  has-unit-Monoid-𝔽 : is-unital mul-Monoid-𝔽
  has-unit-Monoid-𝔽 = pr2 M

  monoid-Monoid-𝔽 : Monoid l
  pr1 monoid-Monoid-𝔽 = semigroup-Monoid-𝔽
  pr2 monoid-Monoid-𝔽 = has-unit-Monoid-𝔽

  unit-Monoid-𝔽 : type-Monoid-𝔽
  unit-Monoid-𝔽 = unit-Monoid monoid-Monoid-𝔽

  left-unit-law-mul-Monoid-𝔽 :
    (x : type-Monoid-𝔽) → mul-Monoid-𝔽 unit-Monoid-𝔽 x ＝ x
  left-unit-law-mul-Monoid-𝔽 = left-unit-law-mul-Monoid monoid-Monoid-𝔽

  right-unit-law-mul-Monoid-𝔽 :
    (x : type-Monoid-𝔽) → mul-Monoid-𝔽 x unit-Monoid-𝔽 ＝ x
  right-unit-law-mul-Monoid-𝔽 = right-unit-law-mul-Monoid monoid-Monoid-𝔽
```

### Monoids of order `n`

```agda
Monoid-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Monoid-of-Order l n = Σ (Monoid l) (λ M → mere-equiv (Fin n) (type-Monoid M))
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

### The type of monoids of order `n` is π-finite

```agda
is-π-finite-Monoid-of-Order :
  {l : Level} (k n : ℕ) → is-π-finite k (Monoid-of-Order l n)
is-π-finite-Monoid-of-Order {l} k n =
  is-π-finite-equiv k e
    ( is-π-finite-Σ k
      ( is-π-finite-Semigroup-of-Order (succ-ℕ k) n)
      ( λ X →
        is-π-finite-is-finite k
          ( is-finite-is-unital-Semigroup n X)))
  where
  e :
    Monoid-of-Order l n ≃
    Σ (Semigroup-of-Order l n) (λ X → is-unital-Semigroup (pr1 X))
  e = equiv-right-swap-Σ
```

### The function that returns for any `n` the number of monoids of order `n` up to isomorphism

```agda
number-of-monoids-of-order : ℕ → ℕ
number-of-monoids-of-order n =
  number-of-connected-components
    ( is-π-finite-Monoid-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-monoids-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-monoids-of-order n))
    ( type-trunc-Set (Monoid-of-Order lzero n))
mere-equiv-number-of-monoids-of-order n =
  mere-equiv-number-of-connected-components
    ( is-π-finite-Monoid-of-Order {lzero} zero-ℕ n)
```

### For any finite semigroup `G`, being unital is a property

```agda
abstract
  is-prop-is-unital-Semigroup-𝔽 :
    {l : Level} (G : Semigroup-𝔽 l) → is-prop (is-unital-Semigroup-𝔽 G)
  is-prop-is-unital-Semigroup-𝔽 G =
    is-prop-is-unital-Semigroup (semigroup-Semigroup-𝔽 G)

is-unital-Semigroup-𝔽-Prop : {l : Level} (G : Semigroup-𝔽 l) → Prop l
pr1 (is-unital-Semigroup-𝔽-Prop G) = is-unital-Semigroup-𝔽 G
pr2 (is-unital-Semigroup-𝔽-Prop G) = is-prop-is-unital-Semigroup-𝔽 G
```

### For any finite semigroup `G`, being unital is finite

```agda
is-finite-is-unital-Semigroup-𝔽 :
  {l : Level} (G : Semigroup-𝔽 l) → is-finite (is-unital-Semigroup-𝔽 G)
is-finite-is-unital-Semigroup-𝔽 G =
  is-finite-Σ
    ( is-finite-type-Semigroup-𝔽 G)
    ( λ e →
      is-finite-product
        ( is-finite-Π
          ( is-finite-type-Semigroup-𝔽 G)
          ( λ x → is-finite-eq-𝔽 (finite-type-Semigroup-𝔽 G)))
        ( is-finite-Π
          ( is-finite-type-Semigroup-𝔽 G)
          ( λ x → is-finite-eq-𝔽 (finite-type-Semigroup-𝔽 G))))
```

### There is a finite number of ways to equip a finite type with the structure of a monoid

```agda
structure-monoid-𝔽 :
  {l1 : Level} → 𝔽 l1 → UU l1
structure-monoid-𝔽 X =
  Σ (structure-semigroup-𝔽 X) (λ p → is-unital-Semigroup-𝔽 (X , p))

finite-monoid-structure-monoid-𝔽 :
  {l : Level} → (X : 𝔽 l) → structure-monoid-𝔽 X → Monoid-𝔽 l
pr1 (finite-monoid-structure-monoid-𝔽 X (a , u)) = X , a
pr2 (finite-monoid-structure-monoid-𝔽 X (a , u)) = u

is-finite-structure-monoid-𝔽 :
  {l : Level} → (X : 𝔽 l) → is-finite (structure-monoid-𝔽 X)
is-finite-structure-monoid-𝔽 X =
  is-finite-Σ
    ( is-finite-structure-semigroup-𝔽 X)
    ( λ m → is-finite-is-unital-Semigroup-𝔽 (X , m))
```
