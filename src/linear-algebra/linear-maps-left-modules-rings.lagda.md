# Linear maps between left modules over rings

```agda
module linear-algebra.linear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "linear map" Agda=is-linear-map-left-module-Ring Disambiguation="over left modules over a ring" WD="linear map" WDID=Q207643}}
between [left modules](linear-algebra.left-modules-rings.md) is a map `f` with
the following properties:

- Additivity: `f (a + b) = f a + f b`
- Homogeneity: `f (c * a) = c * f a`

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  (M : left-module-Ring l2 R) (N : left-module-Ring l3 R)
  (f : type-left-module-Ring R M → type-left-module-Ring R N)
  where

  is-additive-map-prop-left-module-Ring : Prop (l2 ⊔ l3)
  is-additive-map-prop-left-module-Ring =
    Π-Prop
      ( type-left-module-Ring R M)
      ( λ x →
        Π-Prop
          ( type-left-module-Ring R M)
          ( λ y →
            Id-Prop
              ( set-left-module-Ring R N)
              ( f (add-left-module-Ring R M x y))
              ( add-left-module-Ring R N (f x) (f y))))

  is-additive-map-left-module-Ring : UU (l2 ⊔ l3)
  is-additive-map-left-module-Ring =
    type-Prop is-additive-map-prop-left-module-Ring

  is-homogeneous-map-prop-left-module-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-homogeneous-map-prop-left-module-Ring =
    Π-Prop
      ( type-Ring R)
      ( λ c →
        Π-Prop
          ( type-left-module-Ring R M)
          ( λ x →
            Id-Prop
              ( set-left-module-Ring R N)
              ( f (mul-left-module-Ring R M c x))
              ( mul-left-module-Ring R N c (f x))))

  is-homogeneous-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-homogeneous-map-left-module-Ring =
    type-Prop is-homogeneous-map-prop-left-module-Ring

  is-linear-map-prop-left-module-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-linear-map-prop-left-module-Ring =
    is-additive-map-prop-left-module-Ring ∧
    is-homogeneous-map-prop-left-module-Ring

  is-linear-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-linear-map-left-module-Ring =
    type-Prop is-linear-map-prop-left-module-Ring

  is-additive-is-linear-map-left-module-Ring :
    is-linear-map-left-module-Ring →
    (x y : type-left-module-Ring R M) →
    f (add-left-module-Ring R M x y) ＝
    add-left-module-Ring R N (f x) (f y)
  is-additive-is-linear-map-left-module-Ring = pr1

  is-homogeneous-is-linear-map-left-module-Ring :
    is-linear-map-left-module-Ring →
    (c : type-Ring R) (x : type-left-module-Ring R M) →
    f (mul-left-module-Ring R M c x) ＝
    mul-left-module-Ring R N c (f x)
  is-homogeneous-is-linear-map-left-module-Ring = pr2

module _
  {l1 l2 l3 : Level} (R : Ring l1)
  (M : left-module-Ring l2 R) (N : left-module-Ring l3 R)
  where

  linear-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  linear-map-left-module-Ring =
    Σ ( type-left-module-Ring R M → type-left-module-Ring R N)
      ( is-linear-map-left-module-Ring R M N)

  map-linear-map-left-module-Ring :
    linear-map-left-module-Ring →
    type-left-module-Ring R M → type-left-module-Ring R N
  map-linear-map-left-module-Ring = pr1

  is-linear-map-linear-map-left-module-Ring :
    (f : linear-map-left-module-Ring) →
    is-linear-map-left-module-Ring R M N (map-linear-map-left-module-Ring f)
  is-linear-map-linear-map-left-module-Ring = pr2

  is-additive-map-linear-map-left-module-Ring :
    (f : linear-map-left-module-Ring) →
    is-additive-map-left-module-Ring R M N (map-linear-map-left-module-Ring f)
  is-additive-map-linear-map-left-module-Ring =
    is-additive-is-linear-map-left-module-Ring R M N _ ∘
    is-linear-map-linear-map-left-module-Ring

  is-homogeneous-map-linear-map-left-module-Ring :
    (f : linear-map-left-module-Ring) →
    is-homogeneous-map-left-module-Ring R M N
      ( map-linear-map-left-module-Ring f)
  is-homogeneous-map-linear-map-left-module-Ring =
    is-homogeneous-is-linear-map-left-module-Ring R M N _ ∘
    is-linear-map-linear-map-left-module-Ring
```

## Properties

### A linear map maps zero to zero

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  (M : left-module-Ring l2 R) (N : left-module-Ring l3 R)
  where

  abstract
    is-zero-map-zero-linear-map-left-module-Ring :
      (f : linear-map-left-module-Ring R M N) →
      map-linear-map-left-module-Ring R M N f (zero-left-module-Ring R M) ＝
      zero-left-module-Ring R N
    is-zero-map-zero-linear-map-left-module-Ring (f , H , K) =
      equational-reasoning
        f (zero-left-module-Ring R M)
        ＝ f (mul-left-module-Ring R M (zero-Ring R) (zero-left-module-Ring R M))
          by ap f (inv (left-zero-law-mul-left-module-Ring R M _))
        ＝ mul-left-module-Ring R N (zero-Ring R) (f (zero-left-module-Ring R M))
          by K _ _
        ＝ zero-left-module-Ring R N
          by left-zero-law-mul-left-module-Ring R N _
```

### A linear map maps `-x` to the negation of the map of `x`

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  (M : left-module-Ring l2 R) (N : left-module-Ring l3 R)
  where

  abstract
    map-neg-linear-map-left-module-Ring :
      (f : linear-map-left-module-Ring R M N) →
      (x : type-left-module-Ring R M) →
      map-linear-map-left-module-Ring R M N f (neg-left-module-Ring R M x) ＝
      neg-left-module-Ring R N (map-linear-map-left-module-Ring R M N f x)
    map-neg-linear-map-left-module-Ring (f , H , K) x =
      equational-reasoning
        f (neg-left-module-Ring R M x)
        ＝ f (mul-left-module-Ring R M (neg-Ring R (one-Ring R)) x)
          by ap f (inv (mul-neg-one-left-module-Ring R M x))
        ＝ mul-left-module-Ring R N (neg-Ring R (one-Ring R)) (f x)
          by K _ _
        ＝ neg-left-module-Ring R N (f x)
          by mul-neg-one-left-module-Ring R N (f x)
```

### The identity map is linear

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  is-linear-id-left-module-Ring : is-linear-map-left-module-Ring R M M id
  is-linear-id-left-module-Ring = (λ _ _ → refl) , (λ _ _ → refl)

  id-linear-map-left-module-Ring : linear-map-left-module-Ring R M M
  id-linear-map-left-module-Ring = (id , is-linear-id-left-module-Ring)
```

### The composition of linear maps is linear

```agda
module _
  {lr l1 l2 l3 : Level} (R : Ring lr)
  (M : left-module-Ring l1 R)
  (N : left-module-Ring l2 R)
  (K : left-module-Ring l3 R)
  (g : type-left-module-Ring R N → type-left-module-Ring R K)
  (f : type-left-module-Ring R M → type-left-module-Ring R N)
  where

  is-additive-comp-is-additive-map-left-module-Ring :
    is-additive-map-left-module-Ring R N K g →
    is-additive-map-left-module-Ring R M N f →
    is-additive-map-left-module-Ring R M K (g ∘ f)
  is-additive-comp-is-additive-map-left-module-Ring Hg Hf x y =
    ap g (Hf x y) ∙ Hg (f x) (f y)

  is-homogeneous-comp-is-homogeneous-map-left-module-Ring :
    is-homogeneous-map-left-module-Ring R N K g →
    is-homogeneous-map-left-module-Ring R M N f →
    is-homogeneous-map-left-module-Ring R M K (g ∘ f)
  is-homogeneous-comp-is-homogeneous-map-left-module-Ring Hg Hf c x =
    ap g (Hf c x) ∙ Hg c (f x)

  is-linear-comp-is-linear-map-left-module-Ring :
    is-linear-map-left-module-Ring R N K g →
    is-linear-map-left-module-Ring R M N f →
    is-linear-map-left-module-Ring R M K (g ∘ f)
  is-linear-comp-is-linear-map-left-module-Ring Hg Hf =
    ( is-additive-comp-is-additive-map-left-module-Ring
      ( is-additive-is-linear-map-left-module-Ring R N K g Hg)
      ( is-additive-is-linear-map-left-module-Ring R M N f Hf)) ,
    ( is-homogeneous-comp-is-homogeneous-map-left-module-Ring
      ( is-homogeneous-is-linear-map-left-module-Ring R N K g Hg)
      ( is-homogeneous-is-linear-map-left-module-Ring R M N f Hf))
```

### The linear composition of linear maps between left modules

```agda
module _
  {lr l1 l2 l3 : Level} (R : Ring lr)
  (M : left-module-Ring l1 R)
  (N : left-module-Ring l2 R)
  (K : left-module-Ring l3 R)
  (g : linear-map-left-module-Ring R N K)
  (f : linear-map-left-module-Ring R M N)
  where

  comp-linear-map-left-module-Ring : linear-map-left-module-Ring R M K
  comp-linear-map-left-module-Ring =
    ( map-linear-map-left-module-Ring R N K g ∘
      map-linear-map-left-module-Ring R M N f) ,
    ( is-linear-comp-is-linear-map-left-module-Ring R M N K
      ( map-linear-map-left-module-Ring R N K g)
      ( map-linear-map-left-module-Ring R M N f)
      ( is-linear-map-linear-map-left-module-Ring R N K g)
      ( is-linear-map-linear-map-left-module-Ring R M N f))
```
