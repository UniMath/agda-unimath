# Finite semigroups

```agda
module finite-group-theory.finite-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-propositions
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.semigroups

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.function-types
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.standard-finite-types
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
Semigroup-𝔽 : (l : Level) → UU (lsuc l)
Semigroup-𝔽 l = Σ (𝔽 l) (has-associative-mul-𝔽)

module _
  {l : Level} (G : Semigroup-𝔽 l)
  where

  finite-type-Semigroup-𝔽 : 𝔽 l
  finite-type-Semigroup-𝔽 = pr1 G

  set-Semigroup-𝔽 : Set l
  set-Semigroup-𝔽 = set-𝔽 finite-type-Semigroup-𝔽

  type-Semigroup-𝔽 : UU l
  type-Semigroup-𝔽 = type-𝔽 finite-type-Semigroup-𝔽

  is-finite-type-Semigroup-𝔽 : is-finite type-Semigroup-𝔽
  is-finite-type-Semigroup-𝔽 =
    is-finite-type-𝔽 finite-type-Semigroup-𝔽

  is-set-type-Semigroup-𝔽 : is-set type-Semigroup-𝔽
  is-set-type-Semigroup-𝔽 =
    is-set-type-𝔽 finite-type-Semigroup-𝔽

  has-associative-mul-Semigroup-𝔽 :
    has-associative-mul type-Semigroup-𝔽
  has-associative-mul-Semigroup-𝔽 = pr2 G

  semigroup-Semigroup-𝔽 : Semigroup l
  pr1 semigroup-Semigroup-𝔽 = set-Semigroup-𝔽
  pr2 semigroup-Semigroup-𝔽 = has-associative-mul-Semigroup-𝔽

  mul-Semigroup-𝔽 :
    type-Semigroup-𝔽 → type-Semigroup-𝔽 → type-Semigroup-𝔽
  mul-Semigroup-𝔽 = mul-Semigroup semigroup-Semigroup-𝔽

  mul-Semigroup-𝔽' :
    type-Semigroup-𝔽 → type-Semigroup-𝔽 → type-Semigroup-𝔽
  mul-Semigroup-𝔽' = mul-Semigroup' semigroup-Semigroup-𝔽

  associative-mul-Semigroup-𝔽 :
    (x y z : type-Semigroup-𝔽) →
    ( mul-Semigroup-𝔽 (mul-Semigroup-𝔽 x y) z) ＝
    ( mul-Semigroup-𝔽 x (mul-Semigroup-𝔽 y z))
  associative-mul-Semigroup-𝔽 =
    associative-mul-Semigroup semigroup-Semigroup-𝔽

finite-semigroup-is-finite-Semigroup :
  {l : Level} → (G : Semigroup l) → is-finite (type-Semigroup G) → Semigroup-𝔽 l
pr1 (pr1 (finite-semigroup-is-finite-Semigroup G f)) = type-Semigroup G
pr2 (pr1 (finite-semigroup-is-finite-Semigroup G f)) = f
pr2 (finite-semigroup-is-finite-Semigroup G f) = has-associative-mul-Semigroup G

module _
  {l : Level} (G : Semigroup-𝔽 l)
  where

  ap-mul-Semigroup-𝔽 :
    {x x' y y' : type-Semigroup-𝔽 G} →
    x ＝ x' → y ＝ y' → mul-Semigroup-𝔽 G x y ＝ mul-Semigroup-𝔽 G x' y'
  ap-mul-Semigroup-𝔽 = ap-mul-Semigroup (semigroup-Semigroup-𝔽 G)
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

### The type of semigroups of order `n` is π-finite

```agda
is-π-finite-Semigroup-of-Order' :
  {l : Level} (k n : ℕ) → is-π-finite k (Semigroup-of-Order' l n)
is-π-finite-Semigroup-of-Order' k n =
  is-π-finite-Σ k
    ( is-π-finite-UU-Fin (succ-ℕ k) n)
    ( λ x →
      is-π-finite-is-finite k
        ( is-finite-has-associative-mul
          ( is-finite-type-UU-Fin n x)))

is-π-finite-Semigroup-of-Order :
  {l : Level} (k n : ℕ) → is-π-finite k (Semigroup-of-Order l n)
is-π-finite-Semigroup-of-Order {l} k n =
  is-π-finite-equiv k e
    ( is-π-finite-Semigroup-of-Order' k n)
  where
  e : Semigroup-of-Order l n ≃ Semigroup-of-Order' l n
  e = ( equiv-Σ
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

### The function that returns for each `n` the number of semigroups of order `n` up to isomorphism

```agda
number-of-semi-groups-of-order : ℕ → ℕ
number-of-semi-groups-of-order n =
  number-of-connected-components
    ( is-π-finite-Semigroup-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-semi-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-semi-groups-of-order n))
    ( type-trunc-Set (Semigroup-of-Order lzero n))
mere-equiv-number-of-semi-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-π-finite-Semigroup-of-Order {lzero} zero-ℕ n)
```

### There is a finite number of ways to equip a finite type with the structure of a semigroup

```agda
structure-semigroup-𝔽 :
  {l1 : Level} → 𝔽 l1 → UU l1
structure-semigroup-𝔽 = has-associative-mul-𝔽

is-finite-structure-semigroup-𝔽 :
  {l : Level} → (X : 𝔽 l) → is-finite (structure-semigroup-𝔽 X)
is-finite-structure-semigroup-𝔽 X =
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
