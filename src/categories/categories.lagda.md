---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.categories where

open import univalent-foundations public

module _
  {l1 l2 : Level} {A : UU l1} (hom : A → A → UU-Set l2)
  where
  
  associative-composition-structure-Set : UU (l1 ⊔ l2)
  associative-composition-structure-Set =
    Σ ( {x y z : A}
        → type-Set (hom y z)
        → type-Set (hom x y)
        → type-Set (hom x z))
      ( λ μ →
        {x y z w : A} (h : type-Set (hom z w)) (g : type-Set (hom y z))
        (f : type-Set (hom x y)) →
        Id (μ (μ h g) f) (μ h (μ g f)))

  is-unital-composition-structure-Set :
    associative-composition-structure-Set → UU (l1 ⊔ l2)
  is-unital-composition-structure-Set μ =
    Σ ( (x : A) → type-Set (hom x x))
      ( λ e →
        ( {x y : A} (f : type-Set (hom x y)) → Id (pr1 μ (e y) f) f) ×
        ( {x y : A} (f : type-Set (hom x y)) → Id (pr1 μ f (e x)) f))

  abstract
    all-elements-equal-is-unital-composition-structure-Set :
      ( μ : associative-composition-structure-Set) →
      all-elements-equal (is-unital-composition-structure-Set μ)
    all-elements-equal-is-unital-composition-structure-Set
      ( pair μ assoc-μ)
      ( pair e (pair left-unit-law-e right-unit-law-e))
      ( pair e' (pair left-unit-law-e' right-unit-law-e')) =
      eq-subtype
        ( λ x →
          is-prop-prod
            ( is-prop-Π'
              ( λ a →
                is-prop-Π'
                  ( λ b →
                    is-prop-Π
                      ( λ f' →
                        is-set-type-Set (hom a b) (μ (x b) f') f'))))
            ( is-prop-Π'
              ( λ a →
                is-prop-Π'
                  ( λ b →
                    is-prop-Π
                    ( λ f' →
                      is-set-type-Set (hom a b) (μ f' (x a)) f')))))
        ( eq-htpy
          ( λ x →
            ( inv (left-unit-law-e' (e x))) ∙
            ( right-unit-law-e (e' x))))


    is-prop-is-unital-composition-structure-Set :
      ( μ : associative-composition-structure-Set) →
      is-prop (is-unital-composition-structure-Set μ)
    is-prop-is-unital-composition-structure-Set μ =
      is-prop-all-elements-equal
        ( all-elements-equal-is-unital-composition-structure-Set μ)

Precat :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Precat l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → A → UU-Set l2)
        ( λ hom →
          Σ ( associative-composition-structure-Set hom)
            ( is-unital-composition-structure-Set hom)))

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where
  
  obj-Precat : UU l1
  obj-Precat = pr1 C
  
  hom-Precat : (x y : obj-Precat) → UU-Set l2
  hom-Precat = pr1 (pr2 C)

  type-hom-Precat : (x y : obj-Precat) → UU l2
  type-hom-Precat x y = type-Set (hom-Precat x y)

  is-set-type-hom-Precat : (x y : obj-Precat) → is-set (type-hom-Precat x y)
  is-set-type-hom-Precat x y = is-set-type-Set (hom-Precat x y)

  associative-composition-Precat :
    associative-composition-structure-Set hom-Precat
  associative-composition-Precat = pr1 (pr2 (pr2 C))

  comp-Precat : {x y z : obj-Precat} →
    type-hom-Precat y z → type-hom-Precat x y → type-hom-Precat x z
  comp-Precat = pr1 associative-composition-Precat

  comp-Precat' : {x y z : obj-Precat} →
    type-hom-Precat x y → type-hom-Precat y z → type-hom-Precat x z
  comp-Precat' f g = comp-Precat g f

  assoc-comp-Precat :
    {x y z w : obj-Precat} (h : type-hom-Precat z w) (g : type-hom-Precat y z)
    (f : type-hom-Precat x y) →
    Id (comp-Precat (comp-Precat h g) f)
       (comp-Precat h (comp-Precat g f))
  assoc-comp-Precat = pr2 associative-composition-Precat

  is-unital-Precat :
    is-unital-composition-structure-Set
      hom-Precat
      associative-composition-Precat
  is-unital-Precat = pr2 (pr2 (pr2 C))

  id-Precat : {x : obj-Precat} → type-hom-Precat x x
  id-Precat {x} = pr1 is-unital-Precat x

  left-unit-law-comp-Precat :
    {x y : obj-Precat} (f : type-hom-Precat x y) →
    Id (comp-Precat id-Precat f) f
  left-unit-law-comp-Precat = pr1 (pr2 is-unital-Precat)

  right-unit-law-comp-Precat :
    {x y : obj-Precat} (f : type-hom-Precat x y) →
    Id (comp-Precat f id-Precat) f
  right-unit-law-comp-Precat = pr2 (pr2 is-unital-Precat)

  is-iso-Precat : {x y : obj-Precat} (f : type-hom-Precat x y) → UU l2
  is-iso-Precat {x} {y} f =
    Σ ( type-hom-Precat y x)
       ( λ g → Id (comp-Precat f g) id-Precat ×
               Id (comp-Precat g f) id-Precat)

  abstract
    is-proof-irrelevant-is-iso-Precat :
      {x y : obj-Precat} (f : type-hom-Precat x y) →
      is-proof-irrelevant (is-iso-Precat f)
    pr1 (is-proof-irrelevant-is-iso-Precat f H) = H
    pr2
      ( is-proof-irrelevant-is-iso-Precat {x} {y} f
        ( pair g (pair p q)))
        ( pair g' (pair p' q')) =
      eq-subtype
        ( λ h →
          is-prop-prod
            ( is-set-type-hom-Precat y y (comp-Precat f h) id-Precat)
            ( is-set-type-hom-Precat x x (comp-Precat h f) id-Precat))
        ( ( inv (right-unit-law-comp-Precat g)) ∙
          ( ( ap (comp-Precat g) (inv p')) ∙
            ( ( inv (assoc-comp-Precat g f g')) ∙
              ( ( ap (comp-Precat' g') q) ∙
                ( left-unit-law-comp-Precat g')))))

    is-prop-is-iso-Precat :
      {x y : obj-Precat} (f : type-hom-Precat x y) →
      is-prop (is-iso-Precat f)
    is-prop-is-iso-Precat f =
      is-prop-is-proof-irrelevant (is-proof-irrelevant-is-iso-Precat f)

  iso-Precat : (x y : obj-Precat) → UU l2
  iso-Precat x y = Σ (type-hom-Precat x y) is-iso-Precat

  is-set-iso-Precat : (x y : obj-Precat) → is-set (iso-Precat x y)
  is-set-iso-Precat x y =
    is-set-subtype
      is-prop-is-iso-Precat
      (is-set-type-hom-Precat x y)
      
  iso-Precat-Set : (x y : obj-Precat) → UU-Set l2
  pr1 (iso-Precat-Set x y) = iso-Precat x y
  pr2 (iso-Precat-Set x y) = is-set-iso-Precat x y

  is-iso-id-Precat : {x : obj-Precat} → is-iso-Precat (id-Precat {x})
  pr1 is-iso-id-Precat = id-Precat
  pr1 (pr2 is-iso-id-Precat) = left-unit-law-comp-Precat id-Precat
  pr2 (pr2 is-iso-id-Precat) = left-unit-law-comp-Precat id-Precat

  id-iso-Precat : {x : obj-Precat} → iso-Precat x x
  pr1 id-iso-Precat = id-Precat
  pr2 id-iso-Precat = is-iso-id-Precat

  iso-eq-Precat : (x y : obj-Precat) → Id x y → iso-Precat x y
  iso-eq-Precat x .x refl = id-iso-Precat

  is-category-Precat-Prop : UU-Prop (l1 ⊔ l2)
  is-category-Precat-Prop =
    Π-Prop obj-Precat
      ( λ x → Π-Prop obj-Precat (λ y → is-equiv-Prop (iso-eq-Precat x y)))

  is-category-Precat : UU (l1 ⊔ l2)
  is-category-Precat = type-Prop is-category-Precat-Prop

Cat : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cat l1 l2 = Σ (Precat l1 l2) is-category-Precat

module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  precat-Cat : Precat l1 l2
  precat-Cat = pr1 C

  obj-Cat : UU l1
  obj-Cat = obj-Precat precat-Cat

  hom-Cat : obj-Cat → obj-Cat → UU-Set l2
  hom-Cat = hom-Precat precat-Cat

  type-hom-Cat : obj-Cat → obj-Cat → UU l2
  type-hom-Cat = type-hom-Precat precat-Cat

  is-set-type-hom-Cat : (x Y : obj-Cat) → is-set (type-hom-Cat x Y)
  is-set-type-hom-Cat = is-set-type-hom-Precat precat-Cat

  comp-Cat : {x y z : obj-Cat} → type-hom-Cat y z → type-hom-Cat x y → type-hom-Cat x z
  comp-Cat = comp-Precat precat-Cat

  assoc-comp-Cat :
    {x y z w : obj-Cat}
    (h : type-hom-Cat z w) (g : type-hom-Cat y z) (f : type-hom-Cat x y) →
    Id ( comp-Cat (comp-Cat h g) f)
       ( comp-Cat h (comp-Cat g f))
  assoc-comp-Cat = assoc-comp-Precat precat-Cat

  id-Cat : {x : obj-Cat} → type-hom-Cat x x
  id-Cat = id-Precat precat-Cat

  left-unit-law-comp-Cat :
    {x y : obj-Cat} (f : type-hom-Cat x y) → Id (comp-Cat id-Cat f) f
  left-unit-law-comp-Cat = left-unit-law-comp-Precat precat-Cat

  right-unit-law-comp-Cat :
    {x y : obj-Cat} (f : type-hom-Cat x y) → Id (comp-Cat f id-Cat) f
  right-unit-law-comp-Cat = right-unit-law-comp-Precat precat-Cat

  is-iso-Cat : {x y : obj-Cat} (f : type-hom-Cat x y) → UU l2
  is-iso-Cat = is-iso-Precat precat-Cat

  is-prop-is-iso-Cat :
    {x y : obj-Cat} (f : type-hom-Cat x y) → is-prop (is-iso-Cat f)
  is-prop-is-iso-Cat = is-prop-is-iso-Precat precat-Cat

  iso-Cat : (x y : obj-Cat) → UU l2
  iso-Cat = iso-Precat precat-Cat

  is-set-iso-Cat : (x y : obj-Cat) → is-set (iso-Cat x y)
  is-set-iso-Cat = is-set-iso-Precat precat-Cat

  iso-Cat-Set : (x y : obj-Cat) → UU-Set l2
  iso-Cat-Set = iso-Precat-Set precat-Cat

  is-iso-id-Cat : {x : obj-Cat} → is-iso-Cat (id-Cat {x})
  is-iso-id-Cat = is-iso-id-Precat precat-Cat

  id-iso-Cat : {x : obj-Cat} → iso-Cat x x
  id-iso-Cat = id-iso-Precat precat-Cat

  iso-eq-Cat : (x y : obj-Cat) → Id x y → iso-Cat x y
  iso-eq-Cat = iso-eq-Precat precat-Cat

  is-category-Cat : is-category-Precat precat-Cat
  is-category-Cat = pr2 C

  is-1-type-obj-Cat : is-1-type obj-Cat
  is-1-type-obj-Cat x y =
    is-set-is-equiv
      ( iso-Cat x y)
      ( iso-eq-Cat x y)
      ( is-category-Cat x y)
      ( is-set-iso-Cat x y)

  obj-Cat-1-Type : UU-1-Type l1
  pr1 obj-Cat-1-Type = obj-Cat
  pr2 obj-Cat-1-Type = is-1-type-obj-Cat
```

The category of sets and functions.

```agda
Set-Precat : (l : Level) → Precat (lsuc l) l
pr1 (Set-Precat l) = UU-Set l
pr1 (pr2 (Set-Precat l)) = hom-Set
pr1 (pr1 (pr2 (pr2 (Set-Precat l)))) g f = g ∘ f
pr2 (pr1 (pr2 (pr2 (Set-Precat l)))) h g f = refl
pr1 (pr2 (pr2 (pr2 (Set-Precat l)))) x = id
pr1 (pr2 (pr2 (pr2 (pr2 (Set-Precat l))))) f = refl
pr2 (pr2 (pr2 (pr2 (pr2 (Set-Precat l))))) f = refl

id-iso-Set : {l : Level} {x : UU-Set l} → iso-Set x x
id-iso-Set {l} {x} = id-iso-Precat (Set-Precat l) {x}

iso-eq-Set : {l : Level} (x y : UU-Set l) → Id x y → iso-Set x y
iso-eq-Set {l} = iso-eq-Precat (Set-Precat l)

is-category-Set-Precat : (l : Level) → is-category-Precat (Set-Precat l)
is-category-Set-Precat l x =
  fundamental-theorem-id x
    ( id-iso-Set {l} {x})
    ( is-contr-equiv'
      ( Σ (UU-Set l) (type-equiv-Set x))
      ( equiv-tot (equiv-iso-equiv-Set x))
      ( is-contr-total-equiv-Set x))
    ( iso-eq-Set x)

Set-Cat : (l : Level) → Cat (lsuc l) l
pr1 (Set-Cat l) = Set-Precat l
pr2 (Set-Cat l) = is-category-Set-Precat l
```
