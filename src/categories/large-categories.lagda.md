---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.large-categories where

open import univalent-foundations public
open import Agda.Primitive public

record Large-Precat (α : Level → Level) (β : Level → Level → Level) : Setω where
  constructor make-Large-Precat
  field
    obj-Large-Precat :
      (l : Level) → UU (α l)
    hom-Large-Precat :
      {l1 l2 : Level} → obj-Large-Precat l1 → obj-Large-Precat l2 →
      UU-Set (β l1 l2)
    comp-hom-Large-Precat :
      {l1 l2 l3 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      {Z : obj-Large-Precat l3} →
      type-Set (hom-Large-Precat Y Z) → type-Set (hom-Large-Precat X Y) →
      type-Set (hom-Large-Precat X Z)
    id-hom-Large-Precat :
      {l1 : Level} {X : obj-Large-Precat l1} → type-Set (hom-Large-Precat X X)
    associative-comp-hom-Large-Precat :
      {l1 l2 l3 l4 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      {Z : obj-Large-Precat l3} {W : obj-Large-Precat l4} →
      (h : type-Set (hom-Large-Precat Z W))
      (g : type-Set (hom-Large-Precat Y Z))
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-hom-Large-Precat (comp-hom-Large-Precat h g) f)
         ( comp-hom-Large-Precat h (comp-hom-Large-Precat g f))
    left-unit-law-comp-hom-Large-Precat :
      {l1 l2 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-hom-Large-Precat id-hom-Large-Precat f) f
    right-unit-law-comp-hom-Large-Precat :
      {l1 l2 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-hom-Large-Precat f id-hom-Large-Precat) f

open Large-Precat public

Set-Large-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
obj-Large-Precat Set-Large-Precat = UU-Set
hom-Large-Precat Set-Large-Precat = hom-Set
comp-hom-Large-Precat Set-Large-Precat g f = g ∘ f
id-hom-Large-Precat Set-Large-Precat = id
associative-comp-hom-Large-Precat Set-Large-Precat h g f = refl
left-unit-law-comp-hom-Large-Precat Set-Large-Precat f = refl
right-unit-law-comp-hom-Large-Precat Set-Large-Precat f = refl
```

### Isomorphisms in large precategories

```agda

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where

  type-hom-Large-Precat : UU (β l1 l2)
  type-hom-Large-Precat = type-Set (hom-Large-Precat C X Y)

  is-set-type-hom-Large-Precat : is-set type-hom-Large-Precat
  is-set-type-hom-Large-Precat = is-set-type-Set (hom-Large-Precat C X Y)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 l3 : Level}
  {X : obj-Large-Precat C l1} {Y : obj-Large-Precat C l2}
  {Z : obj-Large-Precat C l3}
  where

  ap-comp-hom-Large-Precat :
    {g g' : type-hom-Large-Precat C Y Z} (p : Id g g')
    {f f' : type-hom-Large-Precat C X Y} (q : Id f f') →
    Id ( comp-hom-Large-Precat C g f)
       ( comp-hom-Large-Precat C g' f')
  ap-comp-hom-Large-Precat p q = ap-binary (comp-hom-Large-Precat C) p q

  comp-hom-Large-Precat' :
    type-hom-Large-Precat C X Y → type-hom-Large-Precat C Y Z →
    type-hom-Large-Precat C X Z
  comp-hom-Large-Precat' f g = comp-hom-Large-Precat C g f

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where
  
  is-iso-hom-Large-Precat :
    type-hom-Large-Precat C X Y → UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-hom-Large-Precat f =
    Σ ( type-hom-Large-Precat C Y X)
      ( λ g →
        ( Id (comp-hom-Large-Precat C f g) (id-hom-Large-Precat C)) ×
        ( Id (comp-hom-Large-Precat C g f) (id-hom-Large-Precat C)))

  all-elements-equal-is-iso-hom-Large-Precat :
    (f : type-hom-Large-Precat C X Y)
    (H K : is-iso-hom-Large-Precat f) → Id H K
  all-elements-equal-is-iso-hom-Large-Precat f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-subtype
      ( λ g →
        is-prop-prod
          ( is-set-type-hom-Large-Precat C Y Y
            ( comp-hom-Large-Precat C f g)
            ( id-hom-Large-Precat C))
          ( is-set-type-hom-Large-Precat C X X
            ( comp-hom-Large-Precat C g f)
            ( id-hom-Large-Precat C)))
      ( ( inv (right-unit-law-comp-hom-Large-Precat C g)) ∙
        ( ( ap ( comp-hom-Large-Precat C g) (inv p')) ∙
          ( ( inv (associative-comp-hom-Large-Precat C g f g')) ∙
            ( ( ap ( comp-hom-Large-Precat' C g') q) ∙
              ( left-unit-law-comp-hom-Large-Precat C g')))))

  is-prop-is-iso-hom-Large-Precat :
    (f : type-hom-Large-Precat C X Y) → is-prop (is-iso-hom-Large-Precat f)
  is-prop-is-iso-hom-Large-Precat f =
    is-prop-all-elements-equal (all-elements-equal-is-iso-hom-Large-Precat f)

  type-iso-Large-Precat : UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  type-iso-Large-Precat =
    Σ (type-hom-Large-Precat C X Y) is-iso-hom-Large-Precat

  is-set-type-iso-Large-Precat : is-set type-iso-Large-Precat
  is-set-type-iso-Large-Precat =
    is-set-subtype
      ( is-prop-is-iso-hom-Large-Precat)
      ( is-set-type-hom-Large-Precat C X Y)

  iso-Large-Precat : UU-Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 iso-Large-Precat = type-iso-Large-Precat
  pr2 iso-Large-Precat = is-set-type-iso-Large-Precat

  hom-iso-Large-Precat : type-iso-Large-Precat → type-hom-Large-Precat C X Y
  hom-iso-Large-Precat = pr1

  is-iso-hom-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    is-iso-hom-Large-Precat (hom-iso-Large-Precat f)
  is-iso-hom-iso-Large-Precat f = pr2 f

  hom-inv-iso-Large-Precat : type-iso-Large-Precat → type-hom-Large-Precat C Y X
  hom-inv-iso-Large-Precat f = pr1 (pr2 f)

  issec-hom-inv-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    Id ( comp-hom-Large-Precat C
         ( hom-iso-Large-Precat f)
         ( hom-inv-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  issec-hom-inv-iso-Large-Precat f = pr1 (pr2 (pr2 f))

  isretr-hom-inv-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    Id ( comp-hom-Large-Precat C
         ( hom-inv-iso-Large-Precat f)
         ( hom-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  isretr-hom-inv-iso-Large-Precat f = pr2 (pr2 (pr2 f))

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 : Level} (X : obj-Large-Precat C l1)
  where

  id-iso-Large-Precat : type-iso-Large-Precat C X X
  pr1 id-iso-Large-Precat = id-hom-Large-Precat C
  pr1 (pr2 id-iso-Large-Precat) = id-hom-Large-Precat C
  pr1 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)
  pr2 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)

  iso-eq-Large-Precat :
    (Y : obj-Large-Precat C l1) → Id X Y → type-iso-Large-Precat C X Y
  iso-eq-Large-Precat .X refl = id-iso-Large-Precat

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β)
  where
  
  is-category-Large-Precat : Setω
  is-category-Large-Precat =
    {l : Level} (X Y : obj-Large-Precat C l) →
    is-equiv (iso-eq-Large-Precat C X Y)

record Large-Cat (α : Level → Level) (β : Level → Level → Level) : Setω where
  constructor make-Large-Cat
  field
    precat-Large-Cat : Large-Precat α β
    is-category-Large-Cat : is-category-Large-Precat precat-Large-Cat

open Large-Cat public

module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precat αC βC) (D : Large-Precat αD βD)
  where

  record functor-Large-Precat (γ : Level → Level) : Setω
    where
    constructor make-functor
    field
      obj-functor-Large-Precat :
        {l1 : Level} → obj-Large-Precat C l1 → obj-Large-Precat D (γ l1)
      hom-functor-Large-Precat :
        {l1 l2 : Level}
        {X : obj-Large-Precat C l1} {Y : obj-Large-Precat C l2} →
        type-hom-Large-Precat C X Y →
        type-hom-Large-Precat D
          ( obj-functor-Large-Precat X)
          ( obj-functor-Large-Precat Y)
      preserves-comp-functor-Large-Precat :
        {l1 l2 l3 : Level} {X : obj-Large-Precat C l1}
        {Y : obj-Large-Precat C l2} {Z : obj-Large-Precat C l3}
        (g : type-hom-Large-Precat C Y Z) (f : type-hom-Large-Precat C X Y) →
        Id ( hom-functor-Large-Precat (comp-hom-Large-Precat C g f))
           ( comp-hom-Large-Precat D
             ( hom-functor-Large-Precat g)
             ( hom-functor-Large-Precat f))
      preserves-id-functor-Large-Precat :
        {l1 : Level} (X : obj-Large-Precat C l1) →
        Id ( hom-functor-Large-Precat (id-hom-Large-Precat C {X = X}))
           ( id-hom-Large-Precat D {X = obj-functor-Large-Precat X})

  open functor-Large-Precat public

module _
  {αC αD αE γG γF : Level → Level} {βC βD βE : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD} {E : Large-Precat αE βE}
  where
  
  comp-functor-Large-Precat :
    functor-Large-Precat D E γG → functor-Large-Precat C D γF →
    functor-Large-Precat C E (λ l → γG (γF l))
  obj-functor-Large-Precat (comp-functor-Large-Precat G F) =
    obj-functor-Large-Precat G ∘ obj-functor-Large-Precat F
  hom-functor-Large-Precat (comp-functor-Large-Precat G F) =
    hom-functor-Large-Precat G ∘ hom-functor-Large-Precat F
  preserves-comp-functor-Large-Precat (comp-functor-Large-Precat G F) g f =
    ( ap
      ( hom-functor-Large-Precat G)
      ( preserves-comp-functor-Large-Precat F g f)) ∙
    ( preserves-comp-functor-Large-Precat G
      ( hom-functor-Large-Precat F g)
      ( hom-functor-Large-Precat F f))
  preserves-id-functor-Large-Precat (comp-functor-Large-Precat G F) X =
    ( ap ( hom-functor-Large-Precat G)
         ( preserves-id-functor-Large-Precat F X)) ∙
    ( preserves-id-functor-Large-Precat G (obj-functor-Large-Precat F X))

module _
  {αC : Level → Level} {βC : Level → Level → Level}
  (C : Large-Precat αC βC)
  where
  
  id-functor-Large-Precat : functor-Large-Precat C C (λ l → l)
  obj-functor-Large-Precat id-functor-Large-Precat = id
  hom-functor-Large-Precat id-functor-Large-Precat = id
  preserves-comp-functor-Large-Precat id-functor-Large-Precat g f = refl
  preserves-id-functor-Large-Precat id-functor-Large-Precat X = refl

module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precat αC βC) (D : Large-Precat αD βD)
  (F : functor-Large-Precat C D γF) (G : functor-Large-Precat C D γG)
  where
  
  record natural-transformation-Large-Precat : Setω
    where
    constructor make-natural-transformation
    field
      obj-natural-transformation-Large-Precat :
        {l1 : Level} (X : obj-Large-Precat C l1) →
        type-hom-Large-Precat D
          ( obj-functor-Large-Precat F X)
          ( obj-functor-Large-Precat G X)
      coherence-square-natural-transformation-Large-Precat :
        {l1 l2 : Level} {X : obj-Large-Precat C l1}
        {Y : obj-Large-Precat C l2} (f : type-hom-Large-Precat C X Y) →
        Id ( comp-hom-Large-Precat D
             ( obj-natural-transformation-Large-Precat Y)
             ( hom-functor-Large-Precat F f))
           ( comp-hom-Large-Precat D
             ( hom-functor-Large-Precat G f)
             ( obj-natural-transformation-Large-Precat X))

  open natural-transformation-Large-Precat public

  record natural-isomorphism-Large-Precat : Setω
    where
    constructor make-natural-isomorphism
    field
      obj-natural-isomorphism-Large-Precat :
        {l1 : Level} (X : obj-Large-Precat C l1) →
        type-iso-Large-Precat D
          ( obj-functor-Large-Precat F X)
          ( obj-functor-Large-Precat G X)
      coherence-square-natural-isomorphism-Large-Precat :
        {l1 l2 : Level} {X : obj-Large-Precat C l1}
        {Y : obj-Large-Precat C l2} (f : type-hom-Large-Precat C X Y) →
        Id ( comp-hom-Large-Precat D
             ( hom-iso-Large-Precat D
               ( obj-functor-Large-Precat F Y)
               ( obj-functor-Large-Precat G Y)
               ( obj-natural-isomorphism-Large-Precat Y))
             ( hom-functor-Large-Precat F f))
           ( comp-hom-Large-Precat D
             ( hom-functor-Large-Precat G f)
             ( hom-iso-Large-Precat D
               ( obj-functor-Large-Precat F X)
               ( obj-functor-Large-Precat G X)
               ( obj-natural-isomorphism-Large-Precat X)))
               
  open natural-isomorphism-Large-Precat public

  natural-transformation-natural-isomorphism-Large-Precat :
    natural-isomorphism-Large-Precat → natural-transformation-Large-Precat
  obj-natural-transformation-Large-Precat
    ( natural-transformation-natural-isomorphism-Large-Precat f)
    ( X) =
    hom-iso-Large-Precat D
      ( obj-functor-Large-Precat F X)
      ( obj-functor-Large-Precat G X)
      ( obj-natural-isomorphism-Large-Precat f X)
  coherence-square-natural-transformation-Large-Precat
    ( natural-transformation-natural-isomorphism-Large-Precat f) =
    coherence-square-natural-isomorphism-Large-Precat f

```
