# Large subprecategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.large-subprecategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories funext

open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.sets funext
open import foundation.strictly-involutive-identity-types funext
open import foundation.subtypes funext
open import foundation.universe-levels
```

</details>

## Idea

A **large subprecategory** of a
[large precategory](category-theory.large-precategories.md) `C` consists of a
family of subtypes `P₀`

```text
  P₀ : (l : Level) → subtype _ (obj C l)
```

of the objects of `C` indexed by universe levels, and a family of subtypes `P₁`

```text
  P₁ : {l1 l2 : Level} (X : obj C l1) (Y : obj C l2) →
       P₀ X → P₀ Y → subtype _ (hom X Y)
```

of the morphisms of `C`, such that `P₁` contains all identity morphisms of
objects in `P₀` and is closed under composition.

## Definitions

### Large subprecategories

```agda
record
  Large-Subprecategory
    {α : Level → Level} {β : Level → Level → Level}
    (γ : Level → Level) (δ : Level → Level → Level)
    (C : Large-Precategory α β) : UUω
  where
  field
    subtype-obj-Large-Subprecategory :
      (l : Level) → subtype (γ l) (obj-Large-Precategory C l)

  is-in-obj-Large-Subprecategory :
    {l : Level} → obj-Large-Precategory C l → UU (γ l)
  is-in-obj-Large-Subprecategory {l} =
    is-in-subtype (subtype-obj-Large-Subprecategory l)

  obj-Large-Subprecategory :
    (l : Level) → UU (α l ⊔ γ l)
  obj-Large-Subprecategory l = type-subtype (subtype-obj-Large-Subprecategory l)

  field
    subtype-hom-Large-Subprecategory :
      {l1 l2 : Level}
      (X : obj-Large-Precategory C l1)
      (Y : obj-Large-Precategory C l2) →
      is-in-obj-Large-Subprecategory X →
      is-in-obj-Large-Subprecategory Y →
      subtype (δ l1 l2) (hom-Large-Precategory C X Y)

  is-in-hom-is-in-obj-Large-Subprecategory :
    {l1 l2 : Level}
    {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2}
    (x : is-in-obj-Large-Subprecategory X)
    (y : is-in-obj-Large-Subprecategory Y) →
    hom-Large-Precategory C X Y → UU (δ l1 l2)
  is-in-hom-is-in-obj-Large-Subprecategory {l1} {l2} {X} {Y} x y =
    is-in-subtype (subtype-hom-Large-Subprecategory X Y x y)

  field
    contains-id-Large-Subprecategory :
      {l : Level} (X : obj-Large-Precategory C l) →
      (H : is-in-obj-Large-Subprecategory X) →
      is-in-hom-is-in-obj-Large-Subprecategory H H (id-hom-Large-Precategory C)

    is-closed-under-composition-Large-Subprecategory :
      {l1 l2 l3 : Level}
      (X : obj-Large-Precategory C l1)
      (Y : obj-Large-Precategory C l2)
      (Z : obj-Large-Precategory C l3)
      (g : hom-Large-Precategory C Y Z)
      (f : hom-Large-Precategory C X Y) →
      (K : is-in-obj-Large-Subprecategory X) →
      (L : is-in-obj-Large-Subprecategory Y) →
      (M : is-in-obj-Large-Subprecategory Z) →
      is-in-hom-is-in-obj-Large-Subprecategory L M g →
      is-in-hom-is-in-obj-Large-Subprecategory K L f →
      is-in-hom-is-in-obj-Large-Subprecategory K M
        ( comp-hom-Large-Precategory C g f)

  hom-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Large-Subprecategory l1)
    (Y : obj-Large-Subprecategory l2) → UU (β l1 l2 ⊔ δ l1 l2)
  hom-Large-Subprecategory (X , x) (Y , y) =
    type-subtype (subtype-hom-Large-Subprecategory X Y x y)

  hom-set-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Large-Subprecategory l1)
    (Y : obj-Large-Subprecategory l2) → Set (β l1 l2 ⊔ δ l1 l2)
  hom-set-Large-Subprecategory (X , x) (Y , y) =
    set-subset
      ( hom-set-Large-Precategory C X Y)
      ( subtype-hom-Large-Subprecategory X Y x y)

  is-set-hom-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Large-Subprecategory l1)
    (Y : obj-Large-Subprecategory l2) → is-set (hom-Large-Subprecategory X Y)
  is-set-hom-Large-Subprecategory X Y =
    is-set-type-Set (hom-set-Large-Subprecategory X Y)

  id-hom-Large-Subprecategory :
      {l : Level} (X : obj-Large-Subprecategory l) →
      hom-Large-Subprecategory X X
  id-hom-Large-Subprecategory (X , x) =
    ( id-hom-Large-Precategory C , contains-id-Large-Subprecategory X x)

  comp-hom-Large-Subprecategory :
    {l1 l2 l3 : Level}
    (X : obj-Large-Subprecategory l1)
    (Y : obj-Large-Subprecategory l2)
    (Z : obj-Large-Subprecategory l3) →
    hom-Large-Subprecategory Y Z →
    hom-Large-Subprecategory X Y →
    hom-Large-Subprecategory X Z
  comp-hom-Large-Subprecategory (X , x) (Y , y) (Z , z) (G , g) (F , f) =
    ( comp-hom-Large-Precategory C G F ,
      is-closed-under-composition-Large-Subprecategory X Y Z G F x y z g f)

  associative-comp-hom-Large-Subprecategory :
    {l1 l2 l3 l4 : Level}
    (X : obj-Large-Subprecategory l1)
    (Y : obj-Large-Subprecategory l2)
    (Z : obj-Large-Subprecategory l3)
    (W : obj-Large-Subprecategory l4)
    (h : hom-Large-Subprecategory Z W)
    (g : hom-Large-Subprecategory Y Z)
    (f : hom-Large-Subprecategory X Y) →
    comp-hom-Large-Subprecategory X Y W
      ( comp-hom-Large-Subprecategory Y Z W h g)
      ( f) ＝
    comp-hom-Large-Subprecategory X Z W
      ( h)
      ( comp-hom-Large-Subprecategory X Y Z g f)
  associative-comp-hom-Large-Subprecategory
    ( X , x) (Y , y) (Z , z) (W , w) (H , h) (G , g) (F , f) =
    eq-type-subtype
      ( subtype-hom-Large-Subprecategory X W x w)
      ( associative-comp-hom-Large-Precategory C H G F)

  involutive-eq-associative-comp-hom-Large-Subprecategory :
    {l1 l2 l3 l4 : Level}
    (X : obj-Large-Subprecategory l1)
    (Y : obj-Large-Subprecategory l2)
    (Z : obj-Large-Subprecategory l3)
    (W : obj-Large-Subprecategory l4)
    (h : hom-Large-Subprecategory Z W)
    (g : hom-Large-Subprecategory Y Z)
    (f : hom-Large-Subprecategory X Y) →
    comp-hom-Large-Subprecategory X Y W
      ( comp-hom-Large-Subprecategory Y Z W h g)
      ( f) ＝ⁱ
    comp-hom-Large-Subprecategory X Z W
      ( h)
      ( comp-hom-Large-Subprecategory X Y Z g f)
  involutive-eq-associative-comp-hom-Large-Subprecategory
    X Y Z W h g f =
    involutive-eq-eq (associative-comp-hom-Large-Subprecategory X Y Z W h g f)

  left-unit-law-comp-hom-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Large-Subprecategory l1)
    (Y : obj-Large-Subprecategory l2)
    (f : hom-Large-Subprecategory X Y) →
    comp-hom-Large-Subprecategory X Y Y (id-hom-Large-Subprecategory Y) f ＝ f
  left-unit-law-comp-hom-Large-Subprecategory (X , x) (Y , y) (F , f) =
    eq-type-subtype
      ( subtype-hom-Large-Subprecategory X Y x y)
      ( left-unit-law-comp-hom-Large-Precategory C F)

  right-unit-law-comp-hom-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Large-Subprecategory l1)
    (Y : obj-Large-Subprecategory l2)
    (f : hom-Large-Subprecategory X Y) →
    comp-hom-Large-Subprecategory X X Y f (id-hom-Large-Subprecategory X) ＝ f
  right-unit-law-comp-hom-Large-Subprecategory (X , x) (Y , y) (F , f) =
    eq-type-subtype
      ( subtype-hom-Large-Subprecategory X Y x y)
      ( right-unit-law-comp-hom-Large-Precategory C F)
```

### The underlying large precategory of a large subprecategory

```agda
  large-precategory-Large-Subprecategory :
    Large-Precategory (λ l → α l ⊔ γ l) (λ l1 l2 → β l1 l2 ⊔ δ l1 l2)
  large-precategory-Large-Subprecategory =
    λ where
      .obj-Large-Precategory →
        obj-Large-Subprecategory
      .hom-set-Large-Precategory →
        hom-set-Large-Subprecategory
      .comp-hom-Large-Precategory {X = X} {Y} {Z} →
        comp-hom-Large-Subprecategory X Y Z
      .id-hom-Large-Precategory {X = X} →
        id-hom-Large-Subprecategory X
      .involutive-eq-associative-comp-hom-Large-Precategory
        {X = X} {Y} {Z} {W} →
        involutive-eq-associative-comp-hom-Large-Subprecategory X Y Z W
      .left-unit-law-comp-hom-Large-Precategory {X = X} {Y} →
        left-unit-law-comp-hom-Large-Subprecategory X Y
      .right-unit-law-comp-hom-Large-Precategory {X = X} {Y} →
        right-unit-law-comp-hom-Large-Subprecategory X Y

open Large-Subprecategory public
```
