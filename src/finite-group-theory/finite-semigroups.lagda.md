# Finite semigroups

```agda
module finite-group-theory.finite-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.1-types
open import foundation.decidable-propositions
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.category-of-semigroups
open import group-theory.semigroups

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.function-types
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.untruncated-pi-finite-types
```

</details>

## Idea

Finite semigroups are semigroups of which the underlying type is finite.

## Definitions

### The predicate of having an associative multiplication operation on finite types

```agda
has-associative-mul-𝔽 : {l : Level} (X : 𝔽 l) → UU l
has-associative-mul-𝔽 X = has-associative-mul (type-𝔽 X)
```

### Finite semigroups

```agda
Finite-Semigroup : (l : Level) → UU (lsuc l)
Finite-Semigroup l = Σ (𝔽 l) (has-associative-mul-𝔽)

module _
  {l : Level} (G : Finite-Semigroup l)
  where

  finite-type-Finite-Semigroup : 𝔽 l
  finite-type-Finite-Semigroup = pr1 G

  set-Finite-Semigroup : Set l
  set-Finite-Semigroup = set-𝔽 finite-type-Finite-Semigroup

  type-Finite-Semigroup : UU l
  type-Finite-Semigroup = type-𝔽 finite-type-Finite-Semigroup

  is-finite-type-Finite-Semigroup : is-finite type-Finite-Semigroup
  is-finite-type-Finite-Semigroup =
    is-finite-type-𝔽 finite-type-Finite-Semigroup

  is-set-type-Finite-Semigroup : is-set type-Finite-Semigroup
  is-set-type-Finite-Semigroup =
    is-set-type-𝔽 finite-type-Finite-Semigroup

  has-associative-mul-Finite-Semigroup :
    has-associative-mul type-Finite-Semigroup
  has-associative-mul-Finite-Semigroup = pr2 G

  semigroup-Finite-Semigroup : Semigroup l
  pr1 semigroup-Finite-Semigroup = set-Finite-Semigroup
  pr2 semigroup-Finite-Semigroup = has-associative-mul-Finite-Semigroup

  mul-Finite-Semigroup :
    type-Finite-Semigroup → type-Finite-Semigroup → type-Finite-Semigroup
  mul-Finite-Semigroup = mul-Semigroup semigroup-Finite-Semigroup

  mul-Finite-Semigroup' :
    type-Finite-Semigroup → type-Finite-Semigroup → type-Finite-Semigroup
  mul-Finite-Semigroup' = mul-Semigroup' semigroup-Finite-Semigroup

  associative-mul-Finite-Semigroup :
    (x y z : type-Finite-Semigroup) →
    ( mul-Finite-Semigroup (mul-Finite-Semigroup x y) z) ＝
    ( mul-Finite-Semigroup x (mul-Finite-Semigroup y z))
  associative-mul-Finite-Semigroup =
    associative-mul-Semigroup semigroup-Finite-Semigroup

finite-semigroup-is-finite-Semigroup :
  {l : Level} → (G : Semigroup l) → is-finite (type-Semigroup G) → Finite-Semigroup l
pr1 (pr1 (finite-semigroup-is-finite-Semigroup G f)) = type-Semigroup G
pr2 (pr1 (finite-semigroup-is-finite-Semigroup G f)) = f
pr2 (finite-semigroup-is-finite-Semigroup G f) = has-associative-mul-Semigroup G

module _
  {l : Level} (G : Finite-Semigroup l)
  where

  ap-mul-Finite-Semigroup :
    {x x' y y' : type-Finite-Semigroup G} →
    x ＝ x' → y ＝ y' → mul-Finite-Semigroup G x y ＝ mul-Finite-Semigroup G x' y'
  ap-mul-Finite-Semigroup = ap-mul-Semigroup (semigroup-Finite-Semigroup G)
```

### Semigroups of order `n`

```agda
Semigroup-of-Order' : (l : Level) (n : ℕ) → UU (lsuc l)
Semigroup-of-Order' l n =
  Σ ( UU-Fin l n)
    ( λ X → has-associative-mul (type-UU-Fin n X))

Semigroup-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Semigroup-of-Order l n =
  Σ (Semigroup l) (λ G → mere-equiv (Fin n) (type-Semigroup G))
```

## Properties

### The two definitions of semigroups of order `n` agree

```agda
compute-Semigroup-of-Order :
  {l : Level} (n : ℕ) → Semigroup-of-Order l n ≃ Semigroup-of-Order' l n
compute-Semigroup-of-Order {l} n =
  ( equiv-Σ
    ( has-associative-mul ∘ type-UU-Fin n)
    ( ( right-unit-law-Σ-is-contr
        ( λ X →
          is-proof-irrelevant-is-prop
            ( is-prop-is-set _)
            ( is-set-is-finite (is-finite-has-cardinality n (pr2 X))))) ∘e
      ( equiv-right-swap-Σ))
    ( λ X → id-equiv)) ∘e
  ( equiv-right-swap-Σ
    { A = Set l}
    { B = has-associative-mul-Set}
    { C = mere-equiv (Fin n) ∘ type-Set})
```

### The type of semigroups of order `n` is a 1-type

```agda
is-1-type-Semigroup-of-Order :
  {l : Level} (n : ℕ) → is-1-type (Semigroup-of-Order l n)
is-1-type-Semigroup-of-Order n =
  is-1-type-type-subtype
    ( mere-equiv-Prop (Fin n) ∘ type-Semigroup)
    ( is-1-type-Semigroup)
```

### If `X` is finite, then there are finitely many associative operations on `X`

```agda
is-finite-has-associative-mul :
  {l : Level} {X : UU l} → is-finite X → is-finite (has-associative-mul X)
is-finite-has-associative-mul H =
  is-finite-Σ
    ( is-finite-function-type H (is-finite-function-type H H))
    ( λ μ →
      is-finite-Π H
        ( λ x →
          is-finite-Π H
            ( λ y →
              is-finite-Π H
                ( λ z →
                  is-finite-eq (has-decidable-equality-is-finite H)))))
```

### The type of semigroups of order `n` is π₁-finite

```agda
is-untruncated-π-finite-Semigroup-of-Order' :
  {l : Level} (k n : ℕ) → is-untruncated-π-finite k (Semigroup-of-Order' l n)
is-untruncated-π-finite-Semigroup-of-Order' k n =
  is-untruncated-π-finite-Σ k
    ( is-untruncated-π-finite-UU-Fin (succ-ℕ k) n)
    ( λ x →
      is-untruncated-π-finite-is-finite k
        ( is-finite-has-associative-mul
          ( is-finite-type-UU-Fin n x)))

is-untruncated-π-finite-Semigroup-of-Order :
  {l : Level} (k n : ℕ) → is-untruncated-π-finite k (Semigroup-of-Order l n)
is-untruncated-π-finite-Semigroup-of-Order k n =
  is-untruncated-π-finite-equiv k
    ( compute-Semigroup-of-Order n)
    ( is-untruncated-π-finite-Semigroup-of-Order' k n)

is-π-finite-Semigroup-of-Order :
  {l : Level} (n : ℕ) → is-π-finite 1 (Semigroup-of-Order l n)
is-π-finite-Semigroup-of-Order {l} n =
  is-π-finite-is-untruncated-π-finite 1
    ( is-1-type-Semigroup-of-Order n)
    ( is-untruncated-π-finite-Semigroup-of-Order 1 n)
```

### The number of semigroups of a given order up to isomorphism

The number of semigroups of order `n` is listed as
[A027851](https://oeis.org/A027851) in the [OEIS](literature.oeis.md)
{{#cite oeis}}.

```agda
number-of-semigroups-of-order : ℕ → ℕ
number-of-semigroups-of-order n =
  number-of-connected-components
    ( is-untruncated-π-finite-Semigroup-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-semigroups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-semigroups-of-order n))
    ( type-trunc-Set (Semigroup-of-Order lzero n))
mere-equiv-number-of-semigroups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-untruncated-π-finite-Semigroup-of-Order {lzero} zero-ℕ n)
```

### There is a finite number of ways to equip a finite type with the structure of a semigroup

```agda
structure-finite-semigroup :
  {l1 : Level} → 𝔽 l1 → UU l1
structure-finite-semigroup = has-associative-mul-𝔽

is-finite-structure-finite-semigroup :
  {l : Level} → (X : 𝔽 l) → is-finite (structure-finite-semigroup X)
is-finite-structure-finite-semigroup X =
  is-finite-Σ
    ( is-finite-Π
      ( is-finite-type-𝔽 X)
      ( λ _ → is-finite-Π (is-finite-type-𝔽 X) (λ _ → is-finite-type-𝔽 X)))
    ( λ m →
      is-finite-Π
        ( is-finite-type-𝔽 X)
        ( λ x →
          is-finite-Π
            ( is-finite-type-𝔽 X)
            ( λ y →
              is-finite-Π
                ( is-finite-type-𝔽 X)
                ( λ z →
                  is-finite-is-decidable-Prop
                    ( (m (m x y) z ＝ m x (m y z)) ,
                      is-set-is-finite
                        ( is-finite-type-𝔽 X)
                        ( m (m x y) z)
                        ( m x (m y z)))
                    ( has-decidable-equality-is-finite
                      ( is-finite-type-𝔽 X)
                      ( m (m x y) z)
                      ( m x (m y z)))))))
```

## References

{{#bibliography}}
