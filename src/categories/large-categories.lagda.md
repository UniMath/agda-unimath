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
      {l1 l2 l3 : Level} {x : obj-Large-Precat l1} {y : obj-Large-Precat l2}
      {z : obj-Large-Precat l3} →
      type-Set (hom-Large-Precat y z) → type-Set (hom-Large-Precat x y) →
      type-Set (hom-Large-Precat x z)
    id-hom-Large-Precat :
      {l1 : Level} {x : obj-Large-Precat l1} → type-Set (hom-Large-Precat x x)
    associative-comp-hom-Large-Precat :
      {l1 l2 l3 l4 : Level} {x : obj-Large-Precat l1} {y : obj-Large-Precat l2}
      {z : obj-Large-Precat l3} {w : obj-Large-Precat l4} →
      (h : type-Set (hom-Large-Precat z w))
      (g : type-Set (hom-Large-Precat y z))
      (f : type-Set (hom-Large-Precat x y)) →
      Id ( comp-hom-Large-Precat (comp-hom-Large-Precat h g) f)
         ( comp-hom-Large-Precat h (comp-hom-Large-Precat g f))
    left-unit-law-comp-hom-Large-Precat :
      {l1 l2 : Level} {x : obj-Large-Precat l1} {y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat x y)) →
      Id ( comp-hom-Large-Precat id-hom-Large-Precat f) f
    right-unit-law-comp-hom-Large-Precat :
      {l1 l2 : Level} {x : obj-Large-Precat l1} {y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat x y)) →
      Id ( comp-hom-Large-Precat f id-hom-Large-Precat) f

open Large-Precat public

-- Notation for composition in large categories
_¤_ : {α : Level → Level} {β : Level → Level → Level}
    → ⦃ C : Large-Precat α β ⦄ {l1 l2 l3 : Level}
    → {x : obj-Large-Precat C l1} {y : obj-Large-Precat C l2}
    → {z : obj-Large-Precat C l3}
    → type-Set (hom-Large-Precat C y z)
    → type-Set (hom-Large-Precat C x y)
    → type-Set (hom-Large-Precat C x z)
_¤_ ⦃ C ⦄ = comp-hom-Large-Precat C

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
  (x : obj-Large-Precat C l1) (y : obj-Large-Precat C l2)
  where

  type-hom-Large-Precat : UU (β l1 l2)
  type-hom-Large-Precat = type-Set (hom-Large-Precat C x y)

  is-set-type-hom-Large-Precat : is-set type-hom-Large-Precat
  is-set-type-hom-Large-Precat = is-set-type-Set (hom-Large-Precat C x y)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 l3 : Level}
  {x : obj-Large-Precat C l1} {y : obj-Large-Precat C l2}
  {z : obj-Large-Precat C l3}
  where

  private
    instance
      ⦃C⦄ = C

  ap-comp-hom-Large-Precat :
    {g g' : type-hom-Large-Precat C y z} (p : Id g g')
    {f f' : type-hom-Large-Precat C x y} (q : Id f f') →
    Id (g ¤ f) (g' ¤ f')
  ap-comp-hom-Large-Precat p q = ap-binary (comp-hom-Large-Precat C) p q

  comp-hom-Large-Precat' :
    type-hom-Large-Precat C x y → type-hom-Large-Precat C y z →
    type-hom-Large-Precat C x z
  comp-hom-Large-Precat' f g = g ¤ f

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (x : obj-Large-Precat C l1) (y : obj-Large-Precat C l2)
  where

  private
    instance
      ⦃C⦄ = C
  
  is-iso-hom-Large-Precat :
    type-hom-Large-Precat C x y → UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-hom-Large-Precat f =
    Σ ( type-hom-Large-Precat C y x)
      ( λ g →
        ( Id (f ¤ g) (id-hom-Large-Precat C)) ×
        ( Id (g ¤ f) (id-hom-Large-Precat C)))

  all-elements-equal-is-iso-hom-Large-Precat :
    (f : type-hom-Large-Precat C x y)
    (H K : is-iso-hom-Large-Precat f) → Id H K
  all-elements-equal-is-iso-hom-Large-Precat f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-subtype
      ( λ g →
        is-prop-prod
          ( is-set-type-hom-Large-Precat C y y
            ( f ¤ g)
            ( id-hom-Large-Precat C))
          ( is-set-type-hom-Large-Precat C x x
            ( g ¤ f)
            ( id-hom-Large-Precat C)))
      ( ( inv (right-unit-law-comp-hom-Large-Precat C g)) ∙
        ( ( ap ( comp-hom-Large-Precat C g) (inv p')) ∙
          ( ( inv (associative-comp-hom-Large-Precat C g f g')) ∙
            ( ( ap ( comp-hom-Large-Precat' C g') q) ∙
              ( left-unit-law-comp-hom-Large-Precat C g')))))

  is-prop-is-iso-hom-Large-Precat :
    (f : type-hom-Large-Precat C x y) → is-prop (is-iso-hom-Large-Precat f)
  is-prop-is-iso-hom-Large-Precat f =
    is-prop-all-elements-equal (all-elements-equal-is-iso-hom-Large-Precat f)

  type-iso-Large-Precat : UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  type-iso-Large-Precat =
    Σ (type-hom-Large-Precat C x y) is-iso-hom-Large-Precat

  is-set-type-iso-Large-Precat : is-set type-iso-Large-Precat
  is-set-type-iso-Large-Precat =
    is-set-subtype
      ( is-prop-is-iso-hom-Large-Precat)
      ( is-set-type-hom-Large-Precat C x y)

  iso-Large-Precat : UU-Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 iso-Large-Precat = type-iso-Large-Precat
  pr2 iso-Large-Precat = is-set-type-iso-Large-Precat

  hom-iso-Large-Precat : type-iso-Large-Precat → type-hom-Large-Precat C x y
  hom-iso-Large-Precat = pr1

  is-iso-hom-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    is-iso-hom-Large-Precat (hom-iso-Large-Precat f)
  is-iso-hom-iso-Large-Precat f = pr2 f

  hom-inv-iso-Large-Precat : type-iso-Large-Precat → type-hom-Large-Precat C y x
  hom-inv-iso-Large-Precat f = pr1 (pr2 f)

  issec-hom-inv-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    Id ( ( hom-iso-Large-Precat f) ¤ ( hom-inv-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  issec-hom-inv-iso-Large-Precat f = pr1 (pr2 (pr2 f))

  isretr-hom-inv-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    Id ( ( hom-inv-iso-Large-Precat f) ¤ ( hom-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  isretr-hom-inv-iso-Large-Precat f = pr2 (pr2 (pr2 f))

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 : Level} (x : obj-Large-Precat C l1)
  where

  id-iso-Large-Precat : type-iso-Large-Precat C x x
  pr1 id-iso-Large-Precat = id-hom-Large-Precat C
  pr1 (pr2 id-iso-Large-Precat) = id-hom-Large-Precat C
  pr1 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)
  pr2 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)

  iso-eq-Large-Precat :
    (y : obj-Large-Precat C l1) → Id x y → type-iso-Large-Precat C x y
  iso-eq-Large-Precat .x refl = id-iso-Large-Precat

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β)
  where
  
  is-category-Large-Precat : Setω
  is-category-Large-Precat =
    {l : Level} (x y : obj-Large-Precat C l) →
    is-equiv (iso-eq-Large-Precat C x y)

record Large-Cat (α : Level → Level) (β : Level → Level → Level) : Setω where
  constructor make-Large-Cat
  field
    precat-Large-Cat : Large-Precat α β
    is-category-Large-Cat : is-category-Large-Precat precat-Large-Cat

open Large-Cat public
```

### Functors between large precategories

```agda
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
        {x : obj-Large-Precat C l1} {y : obj-Large-Precat C l2} →
        type-hom-Large-Precat C x y →
        type-hom-Large-Precat D
          ( obj-functor-Large-Precat x)
          ( obj-functor-Large-Precat y)
      preserves-comp-functor-Large-Precat :
        {l1 l2 l3 : Level} {x : obj-Large-Precat C l1}
        {y : obj-Large-Precat C l2} {z : obj-Large-Precat C l3}
        (g : type-hom-Large-Precat C y z) (f : type-hom-Large-Precat C x y) →
        Id ( hom-functor-Large-Precat (comp-hom-Large-Precat C g f))
           ( comp-hom-Large-Precat D
             ( hom-functor-Large-Precat g)
             ( hom-functor-Large-Precat f))
      preserves-id-functor-Large-Precat :
        {l1 : Level} {x : obj-Large-Precat C l1} →
        Id ( hom-functor-Large-Precat (id-hom-Large-Precat C {x = x}))
           ( id-hom-Large-Precat D {x = obj-functor-Large-Precat x})

open functor-Large-Precat public

-- Notation for functors between large categories
_⟨_⟩ : {αC αD : Level → Level} {βC βD : Level → Level → Level}
     → ⦃ C : Large-Precat αC βC ⦄ ⦃ D : Large-Precat αD βD ⦄
     → {γ : Level → Level}
     → functor-Large-Precat C D γ
     → {l1 : Level} → obj-Large-Precat C l1 → obj-Large-Precat D (γ l1)
_⟨_⟩ ⦃ C ⦄ ⦃ D ⦄ = obj-functor-Large-Precat {C = C} {D = D}

_⟪_⟫ : {αC αD : Level → Level} {βC βD : Level → Level → Level}
     → ⦃ C : Large-Precat αC βC ⦄ ⦃ D : Large-Precat αD βD ⦄
     → {γ : Level → Level} (F : functor-Large-Precat C D γ)
     → {l1 l2 : Level} {x : obj-Large-Precat C l1}
     → {y : obj-Large-Precat C l2}
     → type-hom-Large-Precat C x y
     → type-hom-Large-Precat D (F ⟨ x ⟩) (F ⟨ y ⟩)
_⟪_⟫ ⦃ C ⦄ ⦃ D ⦄ = hom-functor-Large-Precat {C = C} {D = D}
```

Every category comes equipped with an identity functor.

```agda
id-functor-Large-Precat : {α : Level → Level} {β : Level → Level → Level}
                        → (C : Large-Precat α β)
                        → functor-Large-Precat C C id
obj-functor-Large-Precat (id-functor-Large-Precat C) = id
hom-functor-Large-Precat (id-functor-Large-Precat C) = id
preserves-comp-functor-Large-Precat (id-functor-Large-Precat C) g f = refl
preserves-id-functor-Large-Precat (id-functor-Large-Precat C) = refl
```

Two compatible functors can be composed.

```agda
comp-functor-Large-Precat : {αC αD αE : Level → Level} {βC βD βE : Level → Level → Level}
                          → (C : Large-Precat αC βC) (D : Large-Precat αD βD) (E : Large-Precat αE βE)
                          → {γF γG : Level → Level}
                          → functor-Large-Precat D E γG
                          → functor-Large-Precat C D γF
                          → functor-Large-Precat C E (γG ∘ γF)
obj-functor-Large-Precat (comp-functor-Large-Precat C D E G F) =
  obj-functor-Large-Precat G ∘ obj-functor-Large-Precat F
hom-functor-Large-Precat (comp-functor-Large-Precat C D E G F) =
  hom-functor-Large-Precat G ∘ hom-functor-Large-Precat F
preserves-comp-functor-Large-Precat (comp-functor-Large-Precat C D E G F) g f =
    ap (G ⟪_⟫) (preserves-comp-functor-Large-Precat F g f)
  ∙ preserves-comp-functor-Large-Precat G (F ⟪ g ⟫) (F ⟪ f ⟫) where
  instance
    ⦃C⦄ = C
    ⦃D⦄ = D
    ⦃E⦄ = E
preserves-id-functor-Large-Precat (comp-functor-Large-Precat C D E G F) =
    ap (G ⟪_⟫) (preserves-id-functor-Large-Precat F)
  ∙ preserves-id-functor-Large-Precat G where
  instance
    ⦃D⦄ = D
    ⦃E⦄ = E

_∘F_ : {αC αD αE : Level → Level} {βC βD βE : Level → Level → Level}
     → ⦃ C : Large-Precat αC βC ⦄ ⦃ D : Large-Precat αD βD ⦄ ⦃ E : Large-Precat αE βE ⦄
     → {γF γG : Level → Level}
     → functor-Large-Precat D E γG
     → functor-Large-Precat C D γF
     → functor-Large-Precat C E (γG ∘ γF)
_∘F_ ⦃ C ⦄ ⦃ D ⦄ ⦃ E ⦄ = comp-functor-Large-Precat C D E
```

### Natural transformations between functors

```agda
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
        {l1 : Level} (x : obj-Large-Precat C l1) →
        type-hom-Large-Precat D
          ( obj-functor-Large-Precat F x)
          ( obj-functor-Large-Precat G x)
      coherence-square-natural-transformation-Large-Precat :
        {l1 l2 : Level} {x : obj-Large-Precat C l1}
        {y : obj-Large-Precat C l2} (f : type-hom-Large-Precat C x y) →
        Id ( comp-hom-Large-Precat D
             ( obj-natural-transformation-Large-Precat y)
             ( hom-functor-Large-Precat F f))
           ( comp-hom-Large-Precat D
             ( hom-functor-Large-Precat G f)
             ( obj-natural-transformation-Large-Precat x))

open natural-transformation-Large-Precat public

-- Notation for natural transformations
_⟹_ : {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
     → ⦃ C : Large-Precat αC βC ⦄ ⦃ D : Large-Precat αD βD ⦄
     → (F : functor-Large-Precat C D γF)
     → (G : functor-Large-Precat C D γG)
     → Setω
_⟹_ ⦃ C ⦄ ⦃ D ⦄ = natural-transformation-Large-Precat C D

_⟦_⟧ : {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
     → ⦃ C : Large-Precat αC βC ⦄ ⦃ D : Large-Precat αD βD ⦄
     → ⦃ F : functor-Large-Precat C D γF ⦄
     → ⦃ G : functor-Large-Precat C D γG ⦄
     → (η : F ⟹ G)
     → {l : Level}
     → (x : obj-Large-Precat C l)
     → type-hom-Large-Precat D (F ⟨ x ⟩) (G ⟨ x ⟩)
_⟦_⟧ ⦃ C ⦄ ⦃ D ⦄ ⦃ F ⦄ ⦃ G ⦄ =
  obj-natural-transformation-Large-Precat {C = C} {D = D} {F = F} {G = G}
```

Every functor comes equipped with an identity natural transformation.

```agda
id-natural-transformation-Large-Precat :
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  → (C : Large-Precat αC βC) (D : Large-Precat αD βD)
  → (F : functor-Large-Precat C D γF)
  → natural-transformation-Large-Precat C D F F
obj-natural-transformation-Large-Precat (id-natural-transformation-Large-Precat C D F) x =
  id-hom-Large-Precat D
coherence-square-natural-transformation-Large-Precat (id-natural-transformation-Large-Precat C D F) f =
    left-unit-law-comp-hom-Large-Precat D (F ⟪ f ⟫)
  ∙ inv (right-unit-law-comp-hom-Large-Precat D (F ⟪ f ⟫)) where
  instance
    ⦃C⦄ = C
    ⦃D⦄ = D
```

### Natural isomorphisms and equivalences of categories

```agda
module _ {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precat αC βC) (D : Large-Precat αD βD)
  (F : functor-Large-Precat C D γF)
  (G : functor-Large-Precat C D γG) where

  private
    instance
      ⦃C⦄ = C
      ⦃D⦄ = D
      ⦃F⦄ = F
      ⦃G⦄ = G

  is-iso-natural-transformation-Large-Precat : F ⟹ G → Setω
  is-iso-natural-transformation-Large-Precat η =
    {l : Level} (x : obj-Large-Precat C l) → is-iso-hom-Large-Precat D (F ⟨ x ⟩) (G ⟨ x ⟩) (η ⟦ x ⟧)

  record natural-isomorphism-Large-Precat : Setω where
    constructor make-natural-isomorphism
    field
      transformation-natural-isomorphism-Large-Precat : natural-transformation-Large-Precat C D F G
      is-iso-natural-isomorphism-Large-Precat :
        is-iso-natural-transformation-Large-Precat transformation-natural-isomorphism-Large-Precat

module _ {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precat αC βC) (D : Large-Precat αD βD) where

  private
    instance
      ⦃C⦄ = C
      ⦃D⦄ = D

  record equivalence-Large-Precat (γ-there γ-back : Level → Level) : Setω where
    constructor make-equivalence-Large-Precat
    field
      there-equivalence-Large-Precat : functor-Large-Precat C D γ-there
      back-equivalence-Large-Precat : functor-Large-Precat D C γ-back
      back-there-equivalence-Large-Precat :
        natural-isomorphism-Large-Precat C C
          (back-equivalence-Large-Precat ∘F there-equivalence-Large-Precat)
          (id-functor-Large-Precat C)
      there-back-equivalence-Large-Precat :
        natural-isomorphism-Large-Precat D D
          (there-equivalence-Large-Precat ∘F back-equivalence-Large-Precat)
          (id-functor-Large-Precat D)
```
