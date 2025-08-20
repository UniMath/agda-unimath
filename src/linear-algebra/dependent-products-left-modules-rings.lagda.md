# Dependent products of left modules over rings

```agda
module linear-algebra.dependent-products-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.dependent-products-abelian-groups

open import linear-algebra.left-modules-rings

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

Given a [ring](ring-theory.rings.md) `R` and a family of
[left modules](linear-algebra.left-modules-rings.md) `Mᵢ` over `R` indexed by
`i : I`, the dependent product `Π (i : I) Mᵢ` is a left module over `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : UU l2)
  (M : I → left-module-Ring l3 R)
  where

  ab-Π-left-module-Ring : Ab (l2 ⊔ l3)
  ab-Π-left-module-Ring = Π-Ab I (ab-left-module-Ring R ∘ M)

  type-Π-left-module-Ring : UU (l2 ⊔ l3)
  type-Π-left-module-Ring = type-Ab ab-Π-left-module-Ring

  add-Π-left-module-Ring :
    type-Π-left-module-Ring → type-Π-left-module-Ring → type-Π-left-module-Ring
  add-Π-left-module-Ring = add-Ab ab-Π-left-module-Ring

  mul-Π-left-module-Ring :
    type-Ring R → type-Π-left-module-Ring → type-Π-left-module-Ring
  mul-Π-left-module-Ring r π i = mul-left-module-Ring R (M i) r (π i)

  left-distributive-mul-add-Π-left-module-Ring :
    (r : type-Ring R) (x y : type-Π-left-module-Ring) →
    mul-Π-left-module-Ring r (add-Π-left-module-Ring x y) ＝
    add-Π-left-module-Ring
      ( mul-Π-left-module-Ring r x)
      ( mul-Π-left-module-Ring r y)
  left-distributive-mul-add-Π-left-module-Ring r x y =
    eq-htpy
      ( λ i → left-distributive-mul-add-left-module-Ring R (M i) r (x i) (y i))

  right-distributive-mul-add-Π-left-module-Ring :
    (r s : type-Ring R) (x : type-Π-left-module-Ring) →
    mul-Π-left-module-Ring (add-Ring R r s) x ＝
    add-Π-left-module-Ring
      ( mul-Π-left-module-Ring r x)
      ( mul-Π-left-module-Ring s x)
  right-distributive-mul-add-Π-left-module-Ring r s x =
    eq-htpy
      ( λ i → right-distributive-mul-add-left-module-Ring R (M i) r s (x i))

  left-unit-law-mul-Π-left-module-Ring :
    (x : type-Π-left-module-Ring) →
    mul-Π-left-module-Ring (one-Ring R) x ＝ x
  left-unit-law-mul-Π-left-module-Ring x =
    eq-htpy (λ i → left-unit-law-mul-left-module-Ring R (M i) (x i))

  associative-mul-Π-left-module-Ring :
    (r s : type-Ring R) (x : type-Π-left-module-Ring) →
    mul-Π-left-module-Ring (mul-Ring R r s) x ＝
    mul-Π-left-module-Ring r (mul-Π-left-module-Ring s x)
  associative-mul-Π-left-module-Ring r s x =
    eq-htpy (λ i → associative-mul-left-module-Ring R (M i) r s (x i))

  Π-left-module-Ring : left-module-Ring (l2 ⊔ l3) R
  Π-left-module-Ring =
    make-left-module-Ring
      ( R)
      ( ab-Π-left-module-Ring)
      ( mul-Π-left-module-Ring)
      ( left-distributive-mul-add-Π-left-module-Ring)
      ( right-distributive-mul-add-Π-left-module-Ring)
      ( left-unit-law-mul-Π-left-module-Ring)
      ( associative-mul-Π-left-module-Ring)
```
