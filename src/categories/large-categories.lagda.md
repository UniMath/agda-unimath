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
```

Notation for composition in large categories

```agda
_∘C_ : {α : Level → Level} {β : Level → Level → Level}
    → ⦃ C : Large-Precat α β ⦄ {l1 l2 l3 : Level}
    → {x : obj-Large-Precat C l1} {y : obj-Large-Precat C l2}
    → {z : obj-Large-Precat C l3}
    → type-Set (hom-Large-Precat C y z)
    → type-Set (hom-Large-Precat C x y)
    → type-Set (hom-Large-Precat C x z)
_∘C_ ⦃ C ⦄ = comp-hom-Large-Precat C
```

The large precategory of sets

```agda
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
  ⦃ C : Large-Precat α β ⦄ {l1 l2 : Level}
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
    {g g' : type-hom-Large-Precat y z} (p : Id g g')
    {f f' : type-hom-Large-Precat x y} (q : Id f f') →
    Id (g ∘C f) (g' ∘C f')
  ap-comp-hom-Large-Precat p q = ap-binary (comp-hom-Large-Precat C) p q

  comp-hom-Large-Precat' :
    type-hom-Large-Precat x y → type-hom-Large-Precat y z →
    type-hom-Large-Precat x z
  comp-hom-Large-Precat' f g = g ∘C f

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (x : obj-Large-Precat C l1) (y : obj-Large-Precat C l2)
  where

  private
    instance
      ⦃C⦄ = C
  
  is-iso-hom-Large-Precat :
    type-hom-Large-Precat x y → UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-hom-Large-Precat f =
    Σ ( type-hom-Large-Precat y x)
      ( λ g →
        ( Id (f ∘C g) (id-hom-Large-Precat C)) ×
        ( Id (g ∘C f) (id-hom-Large-Precat C)))

  all-elements-equal-is-iso-hom-Large-Precat :
    (f : type-hom-Large-Precat x y)
    (H K : is-iso-hom-Large-Precat f) → Id H K
  all-elements-equal-is-iso-hom-Large-Precat f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-subtype
      ( λ g →
        is-prop-prod
          ( is-set-type-hom-Large-Precat y y
            ( f ∘C g)
            ( id-hom-Large-Precat C))
          ( is-set-type-hom-Large-Precat x x
            ( g ∘C f)
            ( id-hom-Large-Precat C)))
      ( ( inv (right-unit-law-comp-hom-Large-Precat C g)) ∙
        ( ( ap ( comp-hom-Large-Precat C g) (inv p')) ∙
          ( ( inv (associative-comp-hom-Large-Precat C g f g')) ∙
            ( ( ap ( comp-hom-Large-Precat' C g') q) ∙
              ( left-unit-law-comp-hom-Large-Precat C g')))))

  is-prop-is-iso-hom-Large-Precat :
    (f : type-hom-Large-Precat x y) → is-prop (is-iso-hom-Large-Precat f)
  is-prop-is-iso-hom-Large-Precat f =
    is-prop-all-elements-equal (all-elements-equal-is-iso-hom-Large-Precat f)

  type-iso-Large-Precat : UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  type-iso-Large-Precat =
    Σ (type-hom-Large-Precat x y) is-iso-hom-Large-Precat

  is-set-type-iso-Large-Precat : is-set type-iso-Large-Precat
  is-set-type-iso-Large-Precat =
    is-set-subtype
      ( is-prop-is-iso-hom-Large-Precat)
      ( is-set-type-hom-Large-Precat x y)

  iso-Large-Precat : UU-Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 iso-Large-Precat = type-iso-Large-Precat
  pr2 iso-Large-Precat = is-set-type-iso-Large-Precat

  hom-iso-Large-Precat : type-iso-Large-Precat → type-hom-Large-Precat x y
  hom-iso-Large-Precat = pr1

  is-iso-hom-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    is-iso-hom-Large-Precat (hom-iso-Large-Precat f)
  is-iso-hom-iso-Large-Precat f = pr2 f

  hom-inv-iso-Large-Precat : type-iso-Large-Precat → type-hom-Large-Precat y x
  hom-inv-iso-Large-Precat f = pr1 (pr2 f)

  issec-hom-inv-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    Id ( ( hom-iso-Large-Precat f) ∘C ( hom-inv-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  issec-hom-inv-iso-Large-Precat f = pr1 (pr2 (pr2 f))

  isretr-hom-inv-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    Id ( ( hom-inv-iso-Large-Precat f) ∘C ( hom-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  isretr-hom-inv-iso-Large-Precat f = pr2 (pr2 (pr2 f))

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 : Level} {x : obj-Large-Precat C l1}
  where

  id-iso-Large-Precat : type-iso-Large-Precat C x x
  pr1 id-iso-Large-Precat = id-hom-Large-Precat C
  pr1 (pr2 id-iso-Large-Precat) = id-hom-Large-Precat C
  pr1 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)
  pr2 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 : Level} (x : obj-Large-Precat C l1)
  where

  iso-eq-Large-Precat :
    (y : obj-Large-Precat C l1) → Id x y → type-iso-Large-Precat C x y
  iso-eq-Large-Precat .x refl = id-iso-Large-Precat C

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

  private
    instance
      ⦃C⦄ = C
      ⦃D⦄ = D

  record functor-Large-Precat (γ : Level → Level) : Setω
    where
    constructor make-functor
    field
      obj-functor-Large-Precat :
        {l1 : Level} → obj-Large-Precat C l1 → obj-Large-Precat D (γ l1)
      hom-functor-Large-Precat :
        {l1 l2 : Level}
        {x : obj-Large-Precat C l1} {y : obj-Large-Precat C l2} →
        type-hom-Large-Precat x y →
        type-hom-Large-Precat
          ( obj-functor-Large-Precat x)
          ( obj-functor-Large-Precat y)
      preserves-comp-functor-Large-Precat :
        {l1 l2 l3 : Level} {x : obj-Large-Precat C l1}
        {y : obj-Large-Precat C l2} {z : obj-Large-Precat C l3}
        (g : type-hom-Large-Precat y z) (f : type-hom-Large-Precat x y) →
        Id ( hom-functor-Large-Precat (comp-hom-Large-Precat C g f))
           ( comp-hom-Large-Precat D
             ( hom-functor-Large-Precat g)
             ( hom-functor-Large-Precat f))
      preserves-id-functor-Large-Precat :
        {l1 : Level} {x : obj-Large-Precat C l1} →
        Id ( hom-functor-Large-Precat (id-hom-Large-Precat C {x = x}))
           ( id-hom-Large-Precat D {x = obj-functor-Large-Precat x})

  open functor-Large-Precat public
```

We introduce notation for functors between large categories

```agda
module _
  {αC αD γ : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  where

  private
    instance
      ⦃C⦄ = C
      ⦃D⦄ = D

  _⟨_⟩ :
    functor-Large-Precat C D γ → {l1 : Level} →
    obj-Large-Precat C l1 → obj-Large-Precat D (γ l1)
  _⟨_⟩ = obj-functor-Large-Precat

  _⟪_⟫ :
    (F : functor-Large-Precat C D γ) {l1 l2 : Level}
    {x : obj-Large-Precat C l1} {y : obj-Large-Precat C l2} →
    type-hom-Large-Precat x y → type-hom-Large-Precat (F ⟨ x ⟩) (F ⟨ y ⟩)
  _⟪_⟫ = hom-functor-Large-Precat
```

Every category comes equipped with an identity functor.

```agda
module _
  {αC : Level → Level} {βC : Level → Level → Level}
  {C : Large-Precat αC βC}
  where
  
  id-functor-Large-Precat : functor-Large-Precat C C (λ l → l)
  obj-functor-Large-Precat id-functor-Large-Precat = id
  hom-functor-Large-Precat id-functor-Large-Precat = id
  preserves-comp-functor-Large-Precat id-functor-Large-Precat g f = refl
  preserves-id-functor-Large-Precat id-functor-Large-Precat = refl
```

Two compatible functors can be composed.

```agda
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
  preserves-id-functor-Large-Precat (comp-functor-Large-Precat G F) =
    ( ap ( hom-functor-Large-Precat G)
         ( preserves-id-functor-Large-Precat F)) ∙
    ( preserves-id-functor-Large-Precat G)

  _∘F_ :
    functor-Large-Precat D E γG → functor-Large-Precat C D γF →
    functor-Large-Precat C E (γG ∘ γF)
  _∘F_ = comp-functor-Large-Precat
```

### Natural transformations between functors

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  (F : functor-Large-Precat C D γF) (G : functor-Large-Precat C D γG)
  where

  private
    instance
      ⦃C⦄ = C
      ⦃D⦄ = D
  
  record natural-transformation-Large-Precat : Setω
    where
    constructor make-natural-transformation
    field
      obj-natural-transformation-Large-Precat :
        {l1 : Level} (x : obj-Large-Precat C l1) →
        type-hom-Large-Precat
          ( obj-functor-Large-Precat F x)
          ( obj-functor-Large-Precat G x)
      coherence-square-natural-transformation-Large-Precat :
        {l1 l2 : Level} {x : obj-Large-Precat C l1}
        {y : obj-Large-Precat C l2} (f : type-hom-Large-Precat x y) →
        Id ( comp-hom-Large-Precat D
             ( obj-natural-transformation-Large-Precat y)
             ( hom-functor-Large-Precat F f))
           ( comp-hom-Large-Precat D
             ( hom-functor-Large-Precat G f)
             ( obj-natural-transformation-Large-Precat x))

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
        {Y : obj-Large-Precat C l2} (f : type-hom-Large-Precat X Y) →
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

-- Notation for natural transformations
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  where

  private
    instance
      ⦃C⦄ = C
      ⦃D⦄ = D
      
  _⟹_ :
    (F : functor-Large-Precat C D γF) (G : functor-Large-Precat C D γG) →
    Setω
  _⟹_ = natural-transformation-Large-Precat
  
  _⟦_⟧ :
    {F : functor-Large-Precat C D γF} {G : functor-Large-Precat C D γG}
    (η : F ⟹ G) {l : Level} (x : obj-Large-Precat C l) →
    type-hom-Large-Precat (F ⟨ x ⟩) (G ⟨ x ⟩)
  _⟦_⟧ = obj-natural-transformation-Large-Precat
```

Every functor comes equipped with an identity natural transformation.

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  where

  private
    instance
      ⦃C⦄ = C
      ⦃D⦄ = D
  
  id-natural-transformation-Large-Precat :
    (F : functor-Large-Precat C D γF) → natural-transformation-Large-Precat F F
  obj-natural-transformation-Large-Precat
    (id-natural-transformation-Large-Precat F) x =
    id-hom-Large-Precat D
  coherence-square-natural-transformation-Large-Precat
    ( id-natural-transformation-Large-Precat F) f =
    ( left-unit-law-comp-hom-Large-Precat D (F ⟪ f ⟫)) ∙
    ( inv (right-unit-law-comp-hom-Large-Precat D (F ⟪ f ⟫)))
```

### The condition on natural transformations of being a natural isomorphism

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  {F : functor-Large-Precat C D γF} {G : functor-Large-Precat C D γG}
  where

  is-iso-natural-transformation-Large-Precat : F ⟹ G → Setω
  is-iso-natural-transformation-Large-Precat η =
    {l : Level} (x : obj-Large-Precat C l) →
    is-iso-hom-Large-Precat D (F ⟨ x ⟩) (G ⟨ x ⟩) (η ⟦ x ⟧)

module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precat αC βC) (D : Large-Precat αD βD)
  where

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
        natural-isomorphism-Large-Precat
          (back-equivalence-Large-Precat ∘F there-equivalence-Large-Precat)
          (id-functor-Large-Precat)
      there-back-equivalence-Large-Precat :
        natural-isomorphism-Large-Precat
          (there-equivalence-Large-Precat ∘F back-equivalence-Large-Precat)
          (id-functor-Large-Precat)
```
