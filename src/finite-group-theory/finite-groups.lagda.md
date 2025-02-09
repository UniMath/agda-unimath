# Finite groups

```agda
module finite-group-theory.finite-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-monoids
open import finite-group-theory.finite-semigroups

open import foundation.1-types
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

open import group-theory.category-of-groups
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
open import univalent-combinatorics.untruncated-pi-finite-types
```

</details>

## Idea

An {{#concept "(abstract) finite group" Agda=Finite-Group}} is a finite group in
the usual algebraic sense, i.e., it consists of a
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
is-group-Finite-Semigroup :
  {l : Level} (G : Finite-Semigroup l) → UU l
is-group-Finite-Semigroup G = is-group-Semigroup (semigroup-Finite-Semigroup G)
```

### The type of finite groups

```agda
Finite-Group :
  (l : Level) → UU (lsuc l)
Finite-Group l = Σ (Finite-Semigroup l) (is-group-Finite-Semigroup)

module _
  {l : Level} (G : Finite-Group l)
  where

  finite-semigroup-Finite-Group : Finite-Semigroup l
  finite-semigroup-Finite-Group = pr1 G

  semigroup-Finite-Group : Semigroup l
  semigroup-Finite-Group =
    semigroup-Finite-Semigroup finite-semigroup-Finite-Group

  is-group-Finite-Group : is-group-Semigroup semigroup-Finite-Group
  is-group-Finite-Group = pr2 G

  group-Finite-Group : Group l
  pr1 group-Finite-Group = semigroup-Finite-Group
  pr2 group-Finite-Group = is-group-Finite-Group

  finite-type-Finite-Group : 𝔽 l
  finite-type-Finite-Group =
    finite-type-Finite-Semigroup finite-semigroup-Finite-Group

  type-Finite-Group : UU l
  type-Finite-Group = type-Group group-Finite-Group

  is-finite-type-Finite-Group : is-finite type-Finite-Group
  is-finite-type-Finite-Group = is-finite-type-𝔽 finite-type-Finite-Group

  has-decidable-equality-Finite-Group : has-decidable-equality type-Finite-Group
  has-decidable-equality-Finite-Group =
    has-decidable-equality-is-finite is-finite-type-Finite-Group

  is-set-type-Finite-Group : is-set type-Finite-Group
  is-set-type-Finite-Group = is-set-type-Group group-Finite-Group

  set-Finite-Group : Set l
  set-Finite-Group = set-Group group-Finite-Group

  has-associative-mul-Finite-Group : has-associative-mul type-Finite-Group
  has-associative-mul-Finite-Group =
    has-associative-mul-Group group-Finite-Group

  mul-Finite-Group : (x y : type-Finite-Group) → type-Finite-Group
  mul-Finite-Group = mul-Group group-Finite-Group

  ap-mul-Finite-Group :
    {x x' y y' : type-Finite-Group} → (x ＝ x') → (y ＝ y') →
    mul-Finite-Group x y ＝ mul-Finite-Group x' y'
  ap-mul-Finite-Group = ap-mul-Group group-Finite-Group

  mul-Finite-Group' : (x y : type-Finite-Group) → type-Finite-Group
  mul-Finite-Group' = mul-Group' group-Finite-Group

  associative-mul-Finite-Group :
    (x y z : type-Finite-Group) →
    ( mul-Finite-Group (mul-Finite-Group x y) z) ＝
    ( mul-Finite-Group x (mul-Finite-Group y z))
  associative-mul-Finite-Group = associative-mul-Group group-Finite-Group

  is-unital-Finite-Group : is-unital-Semigroup semigroup-Finite-Group
  is-unital-Finite-Group = is-unital-Group group-Finite-Group

  monoid-Finite-Group : Monoid l
  monoid-Finite-Group = monoid-Group group-Finite-Group

  unit-Finite-Group : type-Finite-Group
  unit-Finite-Group = unit-Group group-Finite-Group

  is-unit-Finite-Group : type-Finite-Group → UU l
  is-unit-Finite-Group = is-unit-Group group-Finite-Group

  is-decidable-is-unit-Finite-Group :
    (x : type-Finite-Group) → is-decidable (is-unit-Finite-Group x)
  is-decidable-is-unit-Finite-Group x =
    has-decidable-equality-Finite-Group x unit-Finite-Group

  is-prop-is-unit-Finite-Group :
    (x : type-Finite-Group) → is-prop (is-unit-Finite-Group x)
  is-prop-is-unit-Finite-Group = is-prop-is-unit-Group group-Finite-Group

  is-decidable-prop-is-unit-Finite-Group :
    (x : type-Finite-Group) → is-decidable-prop (is-unit-Finite-Group x)
  pr1 (is-decidable-prop-is-unit-Finite-Group x) =
    is-prop-is-unit-Finite-Group x
  pr2 (is-decidable-prop-is-unit-Finite-Group x) =
    is-decidable-is-unit-Finite-Group x

  is-unit-prop-Finite-Group : type-Finite-Group → Prop l
  is-unit-prop-Finite-Group = is-unit-prop-Group group-Finite-Group

  is-unit-finite-group-Decidable-Prop : type-Finite-Group → Decidable-Prop l
  pr1 (is-unit-finite-group-Decidable-Prop x) =
    is-unit-Finite-Group x
  pr2 (is-unit-finite-group-Decidable-Prop x) =
    is-decidable-prop-is-unit-Finite-Group x

  left-unit-law-mul-Finite-Group :
    (x : type-Finite-Group) → mul-Finite-Group unit-Finite-Group x ＝ x
  left-unit-law-mul-Finite-Group =
    left-unit-law-mul-Group group-Finite-Group

  right-unit-law-mul-Finite-Group :
    (x : type-Finite-Group) → mul-Finite-Group x unit-Finite-Group ＝ x
  right-unit-law-mul-Finite-Group =
    right-unit-law-mul-Group group-Finite-Group

  pointed-type-Finite-Group : Pointed-Type l
  pointed-type-Finite-Group = pointed-type-Group group-Finite-Group

  has-inverses-Finite-Group :
    is-group-is-unital-Semigroup semigroup-Finite-Group is-unital-Finite-Group
  has-inverses-Finite-Group = has-inverses-Group group-Finite-Group

  inv-Finite-Group : type-Finite-Group → type-Finite-Group
  inv-Finite-Group = inv-Group group-Finite-Group

  left-inverse-law-mul-Finite-Group :
    (x : type-Finite-Group) →
    mul-Finite-Group (inv-Finite-Group x) x ＝ unit-Finite-Group
  left-inverse-law-mul-Finite-Group =
    left-inverse-law-mul-Group group-Finite-Group

  right-inverse-law-mul-Finite-Group :
    (x : type-Finite-Group) →
    mul-Finite-Group x (inv-Finite-Group x) ＝ unit-Finite-Group
  right-inverse-law-mul-Finite-Group =
    right-inverse-law-mul-Group group-Finite-Group

  inv-unit-Finite-Group :
    inv-Finite-Group unit-Finite-Group ＝ unit-Finite-Group
  inv-unit-Finite-Group = inv-unit-Group group-Finite-Group

  is-section-left-div-Finite-Group :
    (x : type-Finite-Group) →
    ( mul-Finite-Group x ∘ mul-Finite-Group (inv-Finite-Group x)) ~ id
  is-section-left-div-Finite-Group = is-section-left-div-Group group-Finite-Group

  is-retraction-left-div-Finite-Group :
    (x : type-Finite-Group) →
    ( mul-Finite-Group (inv-Finite-Group x) ∘ mul-Finite-Group x) ~ id
  is-retraction-left-div-Finite-Group = is-retraction-left-div-Group group-Finite-Group

  is-equiv-mul-Finite-Group :
    (x : type-Finite-Group) → is-equiv (mul-Finite-Group x)
  is-equiv-mul-Finite-Group = is-equiv-mul-Group group-Finite-Group

  equiv-mul-Finite-Group :
    (x : type-Finite-Group) → type-Finite-Group ≃ type-Finite-Group
  equiv-mul-Finite-Group = equiv-mul-Group group-Finite-Group

  is-section-right-div-Finite-Group :
    (x : type-Finite-Group) →
    (mul-Finite-Group' x ∘ mul-Finite-Group' (inv-Finite-Group x)) ~ id
  is-section-right-div-Finite-Group = is-section-right-div-Group group-Finite-Group

  is-retraction-right-div-Finite-Group :
    (x : type-Finite-Group) →
    (mul-Finite-Group' (inv-Finite-Group x) ∘ mul-Finite-Group' x) ~ id
  is-retraction-right-div-Finite-Group = is-retraction-right-div-Group group-Finite-Group

  is-equiv-mul-Finite-Group' :
    (x : type-Finite-Group) → is-equiv (mul-Finite-Group' x)
  is-equiv-mul-Finite-Group' = is-equiv-mul-Group' group-Finite-Group

  equiv-mul-Finite-Group' :
    (x : type-Finite-Group) → type-Finite-Group ≃ type-Finite-Group
  equiv-mul-Finite-Group' = equiv-mul-Group' group-Finite-Group

  is-binary-equiv-mul-Finite-Group : is-binary-equiv mul-Finite-Group
  is-binary-equiv-mul-Finite-Group =
    is-binary-equiv-mul-Group group-Finite-Group

  is-binary-emb-mul-Finite-Group : is-binary-emb mul-Finite-Group
  is-binary-emb-mul-Finite-Group =
    is-binary-emb-mul-Group group-Finite-Group

  is-emb-mul-Finite-Group :
    (x : type-Finite-Group) → is-emb (mul-Finite-Group x)
  is-emb-mul-Finite-Group = is-emb-mul-Group group-Finite-Group

  is-emb-mul-Finite-Group' :
    (x : type-Finite-Group) → is-emb (mul-Finite-Group' x)
  is-emb-mul-Finite-Group' = is-emb-mul-Group' group-Finite-Group

  is-injective-mul-Finite-Group :
    (x : type-Finite-Group) → is-injective (mul-Finite-Group x)
  is-injective-mul-Finite-Group =
    is-injective-mul-Group group-Finite-Group

  is-injective-mul-Finite-Group' :
    (x : type-Finite-Group) → is-injective (mul-Finite-Group' x)
  is-injective-mul-Finite-Group' =
    is-injective-mul-Group' group-Finite-Group

  transpose-eq-mul-Finite-Group :
    {x y z : type-Finite-Group} →
    (mul-Finite-Group x y ＝ z) → (x ＝ mul-Finite-Group z (inv-Finite-Group y))
  transpose-eq-mul-Finite-Group =
    transpose-eq-mul-Group group-Finite-Group

  transpose-eq-mul-Finite-Group' :
    {x y z : type-Finite-Group} →
    (mul-Finite-Group x y ＝ z) → (y ＝ mul-Finite-Group (inv-Finite-Group x) z)
  transpose-eq-mul-Finite-Group' =
    transpose-eq-mul-Group' group-Finite-Group

  distributive-inv-mul-Finite-Group :
    {x y : type-Finite-Group} →
    ( inv-Finite-Group (mul-Finite-Group x y)) ＝
    ( mul-Finite-Group (inv-Finite-Group y) (inv-Finite-Group x))
  distributive-inv-mul-Finite-Group =
    distributive-inv-mul-Group group-Finite-Group

  inv-inv-Finite-Group :
    (x : type-Finite-Group) → inv-Finite-Group (inv-Finite-Group x) ＝ x
  inv-inv-Finite-Group = inv-inv-Group group-Finite-Group

finite-group-is-finite-Group :
  {l : Level} → (G : Group l) → is-finite (type-Group G) → Finite-Group l
pr1 (finite-group-is-finite-Group G f) =
  finite-semigroup-is-finite-Semigroup (semigroup-Group G) f
pr2 (finite-group-is-finite-Group G f) = is-group-Group G

module _
  {l : Level} (G : Finite-Group l)
  where

  commute-Finite-Group : type-Finite-Group G → type-Finite-Group G → UU l
  commute-Finite-Group = commute-Group (group-Finite-Group G)

  finite-monoid-Finite-Group : Finite-Monoid l
  pr1 finite-monoid-Finite-Group = finite-semigroup-Finite-Group G
  pr2 finite-monoid-Finite-Group = is-unital-Finite-Group G
```

### Groups of fixed finite order

```agda
Group-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Group-of-Order l n = Σ (Group l) (λ G → mere-equiv (Fin n) (type-Group G))

Group-of-Order' : (l : Level) (n : ℕ) → UU (lsuc l)
Group-of-Order' l n =
  Σ (Semigroup-of-Order l n) (λ X → is-group-Semigroup (pr1 X))

compute-Group-of-Order :
  {l : Level} (n : ℕ) → Group-of-Order l n ≃ Group-of-Order' l n
compute-Group-of-Order n = equiv-right-swap-Σ
```

## Properties

### The type of groups of order `n` is a 1-type

```agda
is-1-type-Group-of-Order : {l : Level} (n : ℕ) → is-1-type (Group-of-Order l n)
is-1-type-Group-of-Order n =
  is-1-type-type-subtype (mere-equiv-Prop (Fin n) ∘ type-Group) is-1-type-Group
```

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
```

### The type of groups of order `n` is π₁-finite

```agda
is-untruncated-π-finite-Group-of-Order :
  {l : Level} (k n : ℕ) → is-untruncated-π-finite k (Group-of-Order l n)
is-untruncated-π-finite-Group-of-Order {l} k n =
  is-untruncated-π-finite-equiv k
    ( compute-Group-of-Order n)
    ( is-untruncated-π-finite-Σ k
      ( is-untruncated-π-finite-Semigroup-of-Order (succ-ℕ k) n)
      ( λ X →
        is-untruncated-π-finite-is-finite k
          ( is-finite-is-group-Semigroup n X)))

is-π-finite-Group-of-Order :
  {l : Level} (n : ℕ) → is-π-finite 1 (Group-of-Order l n)
is-π-finite-Group-of-Order n =
  is-π-finite-is-untruncated-π-finite 1
    ( is-1-type-Group-of-Order n)
    ( is-untruncated-π-finite-Group-of-Order 1 n)
```

### The number of groups of a given order up to isomorphism

The number of groups of order `n` is listed as
[A000001](https://oeis.org/A000001) in the [OEIS](literature.oeis.md)
{{#cite oeis}}.

```agda
number-of-groups-of-order : ℕ → ℕ
number-of-groups-of-order n =
  number-of-connected-components
    ( is-untruncated-π-finite-Group-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-groups-of-order n))
    ( type-trunc-Set (Group-of-Order lzero n))
mere-equiv-number-of-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-untruncated-π-finite-Group-of-Order {lzero} zero-ℕ n)
```

### There is a finite number of ways to equip a finite type with the structure of a group

```agda
module _
  {l : Level}
  (X : 𝔽 l)
  where

  structure-group-𝔽 : UU l
  structure-group-𝔽 =
    Σ (structure-semigroup-𝔽 X) (λ s → is-group-Finite-Semigroup (X , s))

  finite-group-structure-group-𝔽 :
    structure-group-𝔽 → Finite-Group l
  pr1 (finite-group-structure-group-𝔽 (s , g)) = (X , s)
  pr2 (finite-group-structure-group-𝔽 (s , g)) = g

  is-finite-structure-group-𝔽 :
    is-finite (structure-group-𝔽)
  is-finite-structure-group-𝔽 =
    is-finite-Σ
      ( is-finite-structure-semigroup-𝔽 X)
      ( λ s →
        is-finite-Σ
          ( is-finite-is-unital-Finite-Semigroup (X , s))
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

## References

{{#bibliography}}
