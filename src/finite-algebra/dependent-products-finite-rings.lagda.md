# Dependent products of finite rings

```agda
module finite-algebra.dependent-products-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-rings

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import ring-theory.dependent-products-rings
open import ring-theory.rings
open import ring-theory.semirings

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Given a family of finite rings `A i` indexed by a finite type `i : I`, their
**dependent product** `Π(i:I), A i` is again a finite ring.

## Definition

```agda
module _
  {l1 l2 : Level} (I : 𝔽 l1) (A : type-𝔽 I → Ring-𝔽 l2)
  where

  semiring-Π-Ring-𝔽 : Semiring (l1 ⊔ l2)
  semiring-Π-Ring-𝔽 = semiring-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  ab-Π-Ring-𝔽 : Ab (l1 ⊔ l2)
  ab-Π-Ring-𝔽 = ab-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  group-Π-Ring-𝔽 : Group (l1 ⊔ l2)
  group-Π-Ring-𝔽 = group-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  semigroup-Π-Ring-𝔽 : Semigroup (l1 ⊔ l2)
  semigroup-Π-Ring-𝔽 = semigroup-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  multiplicative-monoid-Π-Ring-𝔽 : Monoid (l1 ⊔ l2)
  multiplicative-monoid-Π-Ring-𝔽 =
    multiplicative-monoid-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  set-Π-Ring-𝔽 : Set (l1 ⊔ l2)
  set-Π-Ring-𝔽 = set-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  type-Π-Ring-𝔽 : UU (l1 ⊔ l2)
  type-Π-Ring-𝔽 = type-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  is-finite-type-Π-Ring-𝔽 : is-finite (type-Π-Ring-𝔽)
  is-finite-type-Π-Ring-𝔽 =
    is-finite-Π (is-finite-type-𝔽 I) (λ i → is-finite-type-Ring-𝔽 (A i))

  finite-type-Π-Ring-𝔽 : 𝔽 (l1 ⊔ l2)
  pr1 finite-type-Π-Ring-𝔽 = type-Π-Ring-𝔽
  pr2 finite-type-Π-Ring-𝔽 = is-finite-type-Π-Ring-𝔽

  is-set-type-Π-Ring-𝔽 : is-set type-Π-Ring-𝔽
  is-set-type-Π-Ring-𝔽 = is-set-type-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  add-Π-Ring-𝔽 : type-Π-Ring-𝔽 → type-Π-Ring-𝔽 → type-Π-Ring-𝔽
  add-Π-Ring-𝔽 = add-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  zero-Π-Ring-𝔽 : type-Π-Ring-𝔽
  zero-Π-Ring-𝔽 = zero-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  neg-Π-Ring-𝔽 : type-Π-Ring-𝔽 → type-Π-Ring-𝔽
  neg-Π-Ring-𝔽 = neg-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  associative-add-Π-Ring-𝔽 :
    (x y z : type-Π-Ring-𝔽) →
    Id (add-Π-Ring-𝔽 (add-Π-Ring-𝔽 x y) z) (add-Π-Ring-𝔽 x (add-Π-Ring-𝔽 y z))
  associative-add-Π-Ring-𝔽 =
    associative-add-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  left-unit-law-add-Π-Ring-𝔽 :
    (x : type-Π-Ring-𝔽) → Id (add-Π-Ring-𝔽 zero-Π-Ring-𝔽 x) x
  left-unit-law-add-Π-Ring-𝔽 =
    left-unit-law-add-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  right-unit-law-add-Π-Ring-𝔽 :
    (x : type-Π-Ring-𝔽) → Id (add-Π-Ring-𝔽 x zero-Π-Ring-𝔽) x
  right-unit-law-add-Π-Ring-𝔽 =
    right-unit-law-add-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  left-inverse-law-add-Π-Ring-𝔽 :
    (x : type-Π-Ring-𝔽) → Id (add-Π-Ring-𝔽 (neg-Π-Ring-𝔽 x) x) zero-Π-Ring-𝔽
  left-inverse-law-add-Π-Ring-𝔽 =
    left-inverse-law-add-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  right-inverse-law-add-Π-Ring-𝔽 :
    (x : type-Π-Ring-𝔽) → Id (add-Π-Ring-𝔽 x (neg-Π-Ring-𝔽 x)) zero-Π-Ring-𝔽
  right-inverse-law-add-Π-Ring-𝔽 =
    right-inverse-law-add-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  commutative-add-Π-Ring-𝔽 :
    (x y : type-Π-Ring-𝔽) → Id (add-Π-Ring-𝔽 x y) (add-Π-Ring-𝔽 y x)
  commutative-add-Π-Ring-𝔽 =
    commutative-add-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  mul-Π-Ring-𝔽 : type-Π-Ring-𝔽 → type-Π-Ring-𝔽 → type-Π-Ring-𝔽
  mul-Π-Ring-𝔽 = mul-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  one-Π-Ring-𝔽 : type-Π-Ring-𝔽
  one-Π-Ring-𝔽 = one-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  associative-mul-Π-Ring-𝔽 :
    (x y z : type-Π-Ring-𝔽) →
    Id (mul-Π-Ring-𝔽 (mul-Π-Ring-𝔽 x y) z) (mul-Π-Ring-𝔽 x (mul-Π-Ring-𝔽 y z))
  associative-mul-Π-Ring-𝔽 =
    associative-mul-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  left-unit-law-mul-Π-Ring-𝔽 :
    (x : type-Π-Ring-𝔽) → Id (mul-Π-Ring-𝔽 one-Π-Ring-𝔽 x) x
  left-unit-law-mul-Π-Ring-𝔽 =
    left-unit-law-mul-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  right-unit-law-mul-Π-Ring-𝔽 :
    (x : type-Π-Ring-𝔽) → Id (mul-Π-Ring-𝔽 x one-Π-Ring-𝔽) x
  right-unit-law-mul-Π-Ring-𝔽 =
    right-unit-law-mul-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  left-distributive-mul-add-Π-Ring-𝔽 :
    (f g h : type-Π-Ring-𝔽) →
    mul-Π-Ring-𝔽 f (add-Π-Ring-𝔽 g h) ＝
    add-Π-Ring-𝔽 (mul-Π-Ring-𝔽 f g) (mul-Π-Ring-𝔽 f h)
  left-distributive-mul-add-Π-Ring-𝔽 =
    left-distributive-mul-add-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  right-distributive-mul-add-Π-Ring-𝔽 :
    (f g h : type-Π-Ring-𝔽) →
    Id
      ( mul-Π-Ring-𝔽 (add-Π-Ring-𝔽 f g) h)
      ( add-Π-Ring-𝔽 (mul-Π-Ring-𝔽 f h) (mul-Π-Ring-𝔽 g h))
  right-distributive-mul-add-Π-Ring-𝔽 =
    right-distributive-mul-add-Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  ring-Π-Ring-𝔽 : Ring (l1 ⊔ l2)
  ring-Π-Ring-𝔽 = Π-Ring (type-𝔽 I) (ring-Ring-𝔽 ∘ A)

  Π-Ring-𝔽 : Ring-𝔽 (l1 ⊔ l2)
  Π-Ring-𝔽 = compute-ring-𝔽 ring-Π-Ring-𝔽 is-finite-type-Π-Ring-𝔽
```
