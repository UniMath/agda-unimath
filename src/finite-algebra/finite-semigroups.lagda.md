# Finite semigroups

```agda
module finite-algebra.finite-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Finite semigroups are finite sets equipped with an associative binary operation.

## Definition

```agda
has-associative-mul-𝔽 : {l : Level} (X : 𝔽 l) → UU l
has-associative-mul-𝔽 X = has-associative-mul (type-𝔽 X)

Semigroup-𝔽 :
  (l : Level) → UU (lsuc l)
Semigroup-𝔽 l = Σ (𝔽 l) has-associative-mul-𝔽

compute-semigroup-𝔽 :
  {l : Level} → (G : Semigroup l) → is-finite (type-Semigroup G) → Semigroup-𝔽 l
pr1 (pr1 (compute-semigroup-𝔽 G f)) = type-Semigroup G
pr2 (pr1 (compute-semigroup-𝔽 G f)) = f
pr2 (compute-semigroup-𝔽 G f) = has-associative-mul-Semigroup G

module _
  {l : Level} (G : Semigroup-𝔽 l)
  where

  finite-type-Semigroup-𝔽 : 𝔽 l
  finite-type-Semigroup-𝔽 = pr1 G

  type-Semigroup-𝔽 : UU l
  type-Semigroup-𝔽 = type-𝔽 finite-type-Semigroup-𝔽

  is-finite-type-Semigroup-𝔽 : is-finite type-Semigroup-𝔽
  is-finite-type-Semigroup-𝔽 = is-finite-type-𝔽 finite-type-Semigroup-𝔽

  has-associative-mul-Semigroup-𝔽 : has-associative-mul type-Semigroup-𝔽
  has-associative-mul-Semigroup-𝔽 = pr2 G

  semigroup-Semigroup-𝔽 : Semigroup l
  pr1 semigroup-Semigroup-𝔽 = set-𝔽 finite-type-Semigroup-𝔽
  pr2 semigroup-Semigroup-𝔽 = has-associative-mul-Semigroup-𝔽

  set-Semigroup-𝔽 : Set l
  set-Semigroup-𝔽 = set-Semigroup semigroup-Semigroup-𝔽

  is-set-type-Semigroup-𝔽 : is-set type-Semigroup-𝔽
  is-set-type-Semigroup-𝔽 = is-set-type-Semigroup semigroup-Semigroup-𝔽

  mul-Semigroup-𝔽 : type-Semigroup-𝔽 → type-Semigroup-𝔽 → type-Semigroup-𝔽
  mul-Semigroup-𝔽 = mul-Semigroup semigroup-Semigroup-𝔽

  mul-Semigroup-𝔽' : type-Semigroup-𝔽 → type-Semigroup-𝔽 → type-Semigroup-𝔽
  mul-Semigroup-𝔽' = mul-Semigroup' semigroup-Semigroup-𝔽

  ap-mul-Semigroup-𝔽 :
    {x x' y y' : type-Semigroup-𝔽} →
    x ＝ x' → y ＝ y' → mul-Semigroup-𝔽 x y ＝ mul-Semigroup-𝔽 x' y'
  ap-mul-Semigroup-𝔽 = ap-mul-Semigroup semigroup-Semigroup-𝔽

  associative-mul-Semigroup-𝔽 :
    (x y z : type-Semigroup-𝔽) →
    Id
      ( mul-Semigroup-𝔽 (mul-Semigroup-𝔽 x y) z)
      ( mul-Semigroup-𝔽 x (mul-Semigroup-𝔽 y z))
  associative-mul-Semigroup-𝔽 = associative-mul-Semigroup semigroup-Semigroup-𝔽
```

## Properties

### There is a finite number of ways to equip a finite type with a structure of semigroup

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
