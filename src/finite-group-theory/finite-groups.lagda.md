# Finite groups

```agda
module finite-group-theory.finite-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-monoids
open import finite-group-theory.finite-semigroups

open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.commuting-elements-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.pointed-types

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.decidable-propositions
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

An {{#concept "(abstract) finite group" Agda=Group-𝔽}} is a finite group in the
usual algebraic sense, i.e., it consists of a
[finite type](univalent-combinatorics.finite-types.md)
[equipped](foundation.structure.md) with a unit element `e`, a binary operation
`x, y ↦ xy`, and an inverse operation `x ↦ x⁻¹` satisfying the
[group](group-theory.groups.md) laws

```text
  (xy)z = x(yz)      (associativity)
     ex = x          (left unit law)
     xe = x          (right unit law)
   x⁻¹x = e          (left inverse law)
   xx⁻¹ = e          (right inverse law)
```

## Definitions

### The condition that a finite semigroup is a finite group

```agda
is-group-𝔽 :
  {l : Level} (G : Semigroup-𝔽 l) → UU l
is-group-𝔽 G = is-group-Semigroup (semigroup-Semigroup-𝔽 G)
```

### The type of finite groups

```agda
Group-𝔽 :
  (l : Level) → UU (lsuc l)
Group-𝔽 l = Σ (Semigroup-𝔽 l) (is-group-𝔽)

module _
  {l : Level} (G : Group-𝔽 l)
  where

  finite-semigroup-Group-𝔽 : Semigroup-𝔽 l
  finite-semigroup-Group-𝔽 = pr1 G

  semigroup-Group-𝔽 : Semigroup l
  semigroup-Group-𝔽 =
    semigroup-Semigroup-𝔽 finite-semigroup-Group-𝔽

  is-group-Group-𝔽 : is-group-Semigroup semigroup-Group-𝔽
  is-group-Group-𝔽 = pr2 G

  group-Group-𝔽 : Group l
  pr1 group-Group-𝔽 = semigroup-Group-𝔽
  pr2 group-Group-𝔽 = is-group-Group-𝔽

  finite-type-Group-𝔽 : 𝔽 l
  finite-type-Group-𝔽 =
    finite-type-Semigroup-𝔽 finite-semigroup-Group-𝔽

  type-Group-𝔽 : UU l
  type-Group-𝔽 = type-Group group-Group-𝔽

  is-finite-type-Group-𝔽 : is-finite type-Group-𝔽
  is-finite-type-Group-𝔽 = is-finite-type-𝔽 finite-type-Group-𝔽

  has-decidable-equality-Group-𝔽 : has-decidable-equality type-Group-𝔽
  has-decidable-equality-Group-𝔽 =
    has-decidable-equality-is-finite is-finite-type-Group-𝔽

  is-set-type-Group-𝔽 : is-set type-Group-𝔽
  is-set-type-Group-𝔽 = is-set-type-Group group-Group-𝔽

  set-Group-𝔽 : Set l
  set-Group-𝔽 = set-Group group-Group-𝔽

  has-associative-mul-Group-𝔽 : has-associative-mul type-Group-𝔽
  has-associative-mul-Group-𝔽 =
    has-associative-mul-Group group-Group-𝔽

  mul-Group-𝔽 : (x y : type-Group-𝔽) → type-Group-𝔽
  mul-Group-𝔽 = mul-Group group-Group-𝔽

  ap-mul-Group-𝔽 :
    {x x' y y' : type-Group-𝔽} → (x ＝ x') → (y ＝ y') →
    mul-Group-𝔽 x y ＝ mul-Group-𝔽 x' y'
  ap-mul-Group-𝔽 = ap-mul-Group group-Group-𝔽

  mul-Group-𝔽' : (x y : type-Group-𝔽) → type-Group-𝔽
  mul-Group-𝔽' = mul-Group' group-Group-𝔽

  associative-mul-Group-𝔽 :
    (x y z : type-Group-𝔽) →
    ( mul-Group-𝔽 (mul-Group-𝔽 x y) z) ＝
    ( mul-Group-𝔽 x (mul-Group-𝔽 y z))
  associative-mul-Group-𝔽 = associative-mul-Group group-Group-𝔽

  is-unital-Group-𝔽 : is-unital-Semigroup semigroup-Group-𝔽
  is-unital-Group-𝔽 = is-unital-Group group-Group-𝔽

  monoid-Group-𝔽 : Monoid l
  monoid-Group-𝔽 = monoid-Group group-Group-𝔽

  unit-Group-𝔽 : type-Group-𝔽
  unit-Group-𝔽 = unit-Group group-Group-𝔽

  is-unit-Group-𝔽 : type-Group-𝔽 → UU l
  is-unit-Group-𝔽 = is-unit-Group group-Group-𝔽

  is-decidable-is-unit-Group-𝔽 :
    (x : type-Group-𝔽) → is-decidable (is-unit-Group-𝔽 x)
  is-decidable-is-unit-Group-𝔽 x =
    has-decidable-equality-Group-𝔽 x unit-Group-𝔽

  is-prop-is-unit-Group-𝔽 :
    (x : type-Group-𝔽) → is-prop (is-unit-Group-𝔽 x)
  is-prop-is-unit-Group-𝔽 = is-prop-is-unit-Group group-Group-𝔽

  is-decidable-prop-is-unit-Group-𝔽 :
    (x : type-Group-𝔽) → is-decidable-prop (is-unit-Group-𝔽 x)
  pr1 (is-decidable-prop-is-unit-Group-𝔽 x) =
    is-prop-is-unit-Group-𝔽 x
  pr2 (is-decidable-prop-is-unit-Group-𝔽 x) =
    is-decidable-is-unit-Group-𝔽 x

  is-unit-prop-Group-𝔽 : type-Group-𝔽 → Prop l
  is-unit-prop-Group-𝔽 = is-unit-prop-Group group-Group-𝔽

  is-unit-finite-group-Decidable-Prop : type-Group-𝔽 → Decidable-Prop l
  pr1 (is-unit-finite-group-Decidable-Prop x) =
    is-unit-Group-𝔽 x
  pr2 (is-unit-finite-group-Decidable-Prop x) =
    is-decidable-prop-is-unit-Group-𝔽 x

  left-unit-law-mul-Group-𝔽 :
    (x : type-Group-𝔽) → mul-Group-𝔽 unit-Group-𝔽 x ＝ x
  left-unit-law-mul-Group-𝔽 =
    left-unit-law-mul-Group group-Group-𝔽

  right-unit-law-mul-Group-𝔽 :
    (x : type-Group-𝔽) → mul-Group-𝔽 x unit-Group-𝔽 ＝ x
  right-unit-law-mul-Group-𝔽 =
    right-unit-law-mul-Group group-Group-𝔽

  pointed-type-Group-𝔽 : Pointed-Type l
  pointed-type-Group-𝔽 = pointed-type-Group group-Group-𝔽

  has-inverses-Group-𝔽 :
    is-group-is-unital-Semigroup semigroup-Group-𝔽 is-unital-Group-𝔽
  has-inverses-Group-𝔽 = has-inverses-Group group-Group-𝔽

  inv-Group-𝔽 : type-Group-𝔽 → type-Group-𝔽
  inv-Group-𝔽 = inv-Group group-Group-𝔽

  left-inverse-law-mul-Group-𝔽 :
    (x : type-Group-𝔽) →
    mul-Group-𝔽 (inv-Group-𝔽 x) x ＝ unit-Group-𝔽
  left-inverse-law-mul-Group-𝔽 =
    left-inverse-law-mul-Group group-Group-𝔽

  right-inverse-law-mul-Group-𝔽 :
    (x : type-Group-𝔽) →
    mul-Group-𝔽 x (inv-Group-𝔽 x) ＝ unit-Group-𝔽
  right-inverse-law-mul-Group-𝔽 =
    right-inverse-law-mul-Group group-Group-𝔽

  inv-unit-Group-𝔽 :
    inv-Group-𝔽 unit-Group-𝔽 ＝ unit-Group-𝔽
  inv-unit-Group-𝔽 = inv-unit-Group group-Group-𝔽

  is-section-left-div-Group-𝔽 :
    (x : type-Group-𝔽) →
    ( mul-Group-𝔽 x ∘ mul-Group-𝔽 (inv-Group-𝔽 x)) ~ id
  is-section-left-div-Group-𝔽 = is-section-left-div-Group group-Group-𝔽

  is-retraction-left-div-Group-𝔽 :
    (x : type-Group-𝔽) →
    ( mul-Group-𝔽 (inv-Group-𝔽 x) ∘ mul-Group-𝔽 x) ~ id
  is-retraction-left-div-Group-𝔽 = is-retraction-left-div-Group group-Group-𝔽

  is-equiv-mul-Group-𝔽 :
    (x : type-Group-𝔽) → is-equiv (mul-Group-𝔽 x)
  is-equiv-mul-Group-𝔽 = is-equiv-mul-Group group-Group-𝔽

  equiv-mul-Group-𝔽 :
    (x : type-Group-𝔽) → type-Group-𝔽 ≃ type-Group-𝔽
  equiv-mul-Group-𝔽 = equiv-mul-Group group-Group-𝔽

  is-section-right-div-Group-𝔽 :
    (x : type-Group-𝔽) →
    (mul-Group-𝔽' x ∘ mul-Group-𝔽' (inv-Group-𝔽 x)) ~ id
  is-section-right-div-Group-𝔽 = is-section-right-div-Group group-Group-𝔽

  is-retraction-right-div-Group-𝔽 :
    (x : type-Group-𝔽) →
    (mul-Group-𝔽' (inv-Group-𝔽 x) ∘ mul-Group-𝔽' x) ~ id
  is-retraction-right-div-Group-𝔽 = is-retraction-right-div-Group group-Group-𝔽

  is-equiv-mul-Group-𝔽' :
    (x : type-Group-𝔽) → is-equiv (mul-Group-𝔽' x)
  is-equiv-mul-Group-𝔽' = is-equiv-mul-Group' group-Group-𝔽

  equiv-mul-Group-𝔽' :
    (x : type-Group-𝔽) → type-Group-𝔽 ≃ type-Group-𝔽
  equiv-mul-Group-𝔽' = equiv-mul-Group' group-Group-𝔽

  is-binary-equiv-mul-Group-𝔽 : is-binary-equiv mul-Group-𝔽
  is-binary-equiv-mul-Group-𝔽 =
    is-binary-equiv-mul-Group group-Group-𝔽

  is-binary-emb-mul-Group-𝔽 : is-binary-emb mul-Group-𝔽
  is-binary-emb-mul-Group-𝔽 =
    is-binary-emb-mul-Group group-Group-𝔽

  is-emb-mul-Group-𝔽 :
    (x : type-Group-𝔽) → is-emb (mul-Group-𝔽 x)
  is-emb-mul-Group-𝔽 = is-emb-mul-Group group-Group-𝔽

  is-emb-mul-Group-𝔽' :
    (x : type-Group-𝔽) → is-emb (mul-Group-𝔽' x)
  is-emb-mul-Group-𝔽' = is-emb-mul-Group' group-Group-𝔽

  is-injective-mul-Group-𝔽 :
    (x : type-Group-𝔽) → is-injective (mul-Group-𝔽 x)
  is-injective-mul-Group-𝔽 =
    is-injective-mul-Group group-Group-𝔽

  is-injective-mul-Group-𝔽' :
    (x : type-Group-𝔽) → is-injective (mul-Group-𝔽' x)
  is-injective-mul-Group-𝔽' =
    is-injective-mul-Group' group-Group-𝔽

  transpose-eq-mul-Group-𝔽 :
    {x y z : type-Group-𝔽} →
    (mul-Group-𝔽 x y ＝ z) → (x ＝ mul-Group-𝔽 z (inv-Group-𝔽 y))
  transpose-eq-mul-Group-𝔽 =
    transpose-eq-mul-Group group-Group-𝔽

  transpose-eq-mul-Group-𝔽' :
    {x y z : type-Group-𝔽} →
    (mul-Group-𝔽 x y ＝ z) → (y ＝ mul-Group-𝔽 (inv-Group-𝔽 x) z)
  transpose-eq-mul-Group-𝔽' =
    transpose-eq-mul-Group' group-Group-𝔽

  distributive-inv-mul-Group-𝔽 :
    {x y : type-Group-𝔽} →
    ( inv-Group-𝔽 (mul-Group-𝔽 x y)) ＝
    ( mul-Group-𝔽 (inv-Group-𝔽 y) (inv-Group-𝔽 x))
  distributive-inv-mul-Group-𝔽 =
    distributive-inv-mul-Group group-Group-𝔽

  inv-inv-Group-𝔽 :
    (x : type-Group-𝔽) → inv-Group-𝔽 (inv-Group-𝔽 x) ＝ x
  inv-inv-Group-𝔽 = inv-inv-Group group-Group-𝔽

finite-group-is-finite-Group :
  {l : Level} → (G : Group l) → is-finite (type-Group G) → Group-𝔽 l
pr1 (finite-group-is-finite-Group G f) =
  finite-semigroup-is-finite-Semigroup (semigroup-Group G) f
pr2 (finite-group-is-finite-Group G f) = is-group-Group G

module _
  {l : Level} (G : Group-𝔽 l)
  where

  commute-Group-𝔽 : type-Group-𝔽 G → type-Group-𝔽 G → UU l
  commute-Group-𝔽 = commute-Group (group-Group-𝔽 G)

  finite-monoid-Group-𝔽 : Monoid-𝔽 l
  pr1 finite-monoid-Group-𝔽 = finite-semigroup-Group-𝔽 G
  pr2 finite-monoid-Group-𝔽 = is-unital-Group-𝔽 G
```

### Groups of fixed finite order

```agda
Group-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Group-of-Order l n = Σ (Group l) (λ G → mere-equiv (Fin n) (type-Group G))
```

## Properties

### The type `is-group-Semigroup G` is finite for any semigroup of fixed finite order

```agda
is-finite-is-group-Semigroup :
  {l : Level} (n : ℕ) (G : Semigroup-of-Order l n) →
  is-finite {l} (is-group-Semigroup (pr1 G))
is-finite-is-group-Semigroup {l} n G =
  apply-universal-property-trunc-Prop
    ( pr2 G)
    ( is-finite-Prop _)
    ( λ e →
      is-finite-is-decidable-Prop
        ( is-group-prop-Semigroup (pr1 G))
        ( is-decidable-Σ-count
          ( count-Σ
            ( pair n e)
            ( λ u →
              count-product
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semigroup (pr1 G) u x)
                      ( x)))
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semigroup (pr1 G) x u)
                      ( x)))))
          ( λ u →
            is-decidable-Σ-count
              ( count-function-type (pair n e) (pair n e))
              ( λ i →
                is-decidable-product
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semigroup (pr1 G) (i x) x)
                        ( pr1 u)))
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semigroup (pr1 G) x (i x))
                        ( pr1 u)))))))

is-π-finite-Group-of-Order :
  {l : Level} (k n : ℕ) → is-π-finite k (Group-of-Order l n)
is-π-finite-Group-of-Order {l} k n =
  is-π-finite-equiv k e
    ( is-π-finite-Σ k
      ( is-π-finite-Semigroup-of-Order (succ-ℕ k) n)
      ( λ X →
        is-π-finite-is-finite k
          ( is-finite-is-group-Semigroup n X)))
  where
  e :
    Group-of-Order l n ≃
    Σ (Semigroup-of-Order l n) (λ X → is-group-Semigroup (pr1 X))
  e = equiv-right-swap-Σ

number-of-groups-of-order : ℕ → ℕ
number-of-groups-of-order n =
  number-of-connected-components
    ( is-π-finite-Group-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-groups-of-order n))
    ( type-trunc-Set (Group-of-Order lzero n))
mere-equiv-number-of-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-π-finite-Group-of-Order {lzero} zero-ℕ n)
```

### There is a finite number of ways to equip a finite type with the structure of a group

```agda
module _
  {l : Level}
  (X : 𝔽 l)
  where

  structure-group-𝔽 : UU l
  structure-group-𝔽 =
    Σ (structure-semigroup-𝔽 X) (λ s → is-group-𝔽 (X , s))

  finite-group-structure-group-𝔽 :
    structure-group-𝔽 → Group-𝔽 l
  pr1 (finite-group-structure-group-𝔽 (s , g)) = (X , s)
  pr2 (finite-group-structure-group-𝔽 (s , g)) = g

  is-finite-structure-group-𝔽 :
    is-finite (structure-group-𝔽)
  is-finite-structure-group-𝔽 =
    is-finite-Σ
      ( is-finite-structure-semigroup-𝔽 X)
      ( λ s →
        is-finite-Σ
          ( is-finite-is-unital-Semigroup-𝔽 (X , s))
          ( λ u →
            is-finite-Σ
              ( is-finite-Π
                ( is-finite-type-𝔽 X)
                ( λ _ → is-finite-type-𝔽 X))
              ( λ i →
                is-finite-product
                  ( is-finite-Π
                    ( is-finite-type-𝔽 X)
                    ( λ x → is-finite-eq-𝔽 X))
                  ( is-finite-Π
                    ( is-finite-type-𝔽 X)
                    ( λ x → is-finite-eq-𝔽 X)))))
```
