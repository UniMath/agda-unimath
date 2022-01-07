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
```

Notation for composition in large categories

```agda
_∘Precat_ : {α : Level → Level} {β : Level → Level → Level}
    → ⦃ C : Large-Precat α β ⦄ {l1 l2 l3 : Level}
    → {X : obj-Large-Precat C l1} {Y : obj-Large-Precat C l2}
    → {Z : obj-Large-Precat C l3}
    → type-Set (hom-Large-Precat C Y Z)
    → type-Set (hom-Large-Precat C X Y)
    → type-Set (hom-Large-Precat C X Z)
_∘Precat_ ⦃ C ⦄ = comp-hom-Large-Precat C
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

  private
    instance
      ⦃C⦄ = C

  ap-comp-hom-Large-Precat :
    {g g' : type-hom-Large-Precat C Y Z} (p : Id g g')
    {f f' : type-hom-Large-Precat C X Y} (q : Id f f') →
    Id (g ∘Precat f) (g' ∘Precat f')
  ap-comp-hom-Large-Precat p q = ap-binary (comp-hom-Large-Precat C) p q

  comp-hom-Large-Precat' :
    type-hom-Large-Precat C X Y → type-hom-Large-Precat C Y Z →
    type-hom-Large-Precat C X Z
  comp-hom-Large-Precat' f g = g ∘Precat f

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where

  private
    instance
      ⦃C⦄ = C

  is-iso-hom-Large-Precat :
    type-hom-Large-Precat C X Y → UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-hom-Large-Precat f =
    Σ ( type-hom-Large-Precat C Y X)
      ( λ g →
        ( Id (f ∘Precat g) (id-hom-Large-Precat C)) ×
        ( Id (g ∘Precat f) (id-hom-Large-Precat C)))

  all-elements-equal-is-iso-hom-Large-Precat :
    (f : type-hom-Large-Precat C X Y)
    (H K : is-iso-hom-Large-Precat f) → Id H K
  all-elements-equal-is-iso-hom-Large-Precat f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-subtype
      ( λ g →
        is-prop-prod
          ( is-set-type-hom-Large-Precat C Y Y
            ( f ∘Precat g)
            ( id-hom-Large-Precat C))
          ( is-set-type-hom-Large-Precat C X X
            ( g ∘Precat f)
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
    Id ( ( hom-iso-Large-Precat f) ∘Precat ( hom-inv-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  issec-hom-inv-iso-Large-Precat f = pr1 (pr2 (pr2 f))

  isretr-hom-inv-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    Id ( ( hom-inv-iso-Large-Precat f) ∘Precat ( hom-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  isretr-hom-inv-iso-Large-Precat f = pr2 (pr2 (pr2 f))

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 : Level} {X : obj-Large-Precat C l1}
  where

  id-iso-Large-Precat : type-iso-Large-Precat C X X
  pr1 id-iso-Large-Precat = id-hom-Large-Precat C
  pr1 (pr2 id-iso-Large-Precat) = id-hom-Large-Precat C
  pr1 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)
  pr2 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 : Level} (X : obj-Large-Precat C l1)
  where

  iso-eq-Large-Precat :
    (Y : obj-Large-Precat C l1) → Id X Y → type-iso-Large-Precat C X Y
  iso-eq-Large-Precat .X refl = id-iso-Large-Precat C

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
        {l1 : Level} {X : obj-Large-Precat C l1} →
        Id ( hom-functor-Large-Precat (id-hom-Large-Precat C {X = X}))
           ( id-hom-Large-Precat D {X = obj-functor-Large-Precat X})

  open functor-Large-Precat public
```

We introduce notation for functors between large categories

```agda
module _
  {αC αD γ : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  where

  _on-obj_ :
    functor-Large-Precat C D γ → {l1 : Level} →
    obj-Large-Precat C l1 → obj-Large-Precat D (γ l1)
  _on-obj_ = obj-functor-Large-Precat

  _on-mor_ :
    (F : functor-Large-Precat C D γ) {l1 l2 : Level}
    {X : obj-Large-Precat C l1} {Y : obj-Large-Precat C l2} →
    type-hom-Large-Precat C X Y → type-hom-Large-Precat D (F on-obj X) (F on-obj Y)
  _on-mor_ = hom-functor-Large-Precat
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

  _∘Functor_ :
    functor-Large-Precat D E γG → functor-Large-Precat C D γF →
    functor-Large-Precat C E (γG ∘ γF)
  _∘Functor_ = comp-functor-Large-Precat
```

### Natural transformations between functors

```agda
module _
  {αC : Level → Level} {βC : Level → Level → Level}
  (C : Large-Precat αC βC)
  {l1 l2 l3 l4 : Level}
  {A : obj-Large-Precat C l1} {B : obj-Large-Precat C l2}
  {X : obj-Large-Precat C l3} {Y : obj-Large-Precat C l4}  
  where

  private
    instance
      ⦃C⦄ = C

  square-Large-Precat :
    (top : type-hom-Large-Precat C A B) (left : type-hom-Large-Precat C A X)
    (right : type-hom-Large-Precat C B Y) (bottom : type-hom-Large-Precat C X Y) →
    UU (βC l1 l4)
  square-Large-Precat top left right bottom =
    Id (bottom ∘Precat left) (right ∘Precat top)

module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
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
        square-Large-Precat D
          ( obj-natural-transformation-Large-Precat X)
          ( hom-functor-Large-Precat F f)
          ( hom-functor-Large-Precat G f)
          ( obj-natural-transformation-Large-Precat Y)

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
        square-Large-Precat D
          ( hom-iso-Large-Precat D
            ( obj-functor-Large-Precat F X)
            ( obj-functor-Large-Precat G X)
            ( obj-natural-isomorphism-Large-Precat X))
          ( hom-functor-Large-Precat F f)
          ( hom-functor-Large-Precat G f)
          ( hom-iso-Large-Precat D
            ( obj-functor-Large-Precat F Y)
            ( obj-functor-Large-Precat G Y)
            ( obj-natural-isomorphism-Large-Precat Y))
               
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
      
  _⟹_ :
    (F : functor-Large-Precat C D γF) (G : functor-Large-Precat C D γG) →
    Setω
  _⟹_ = natural-transformation-Large-Precat

  natural-transformation_at_ :
    {F : functor-Large-Precat C D γF} {G : functor-Large-Precat C D γG}
    (η : F ⟹ G) {l : Level} (X : obj-Large-Precat C l) →
    type-hom-Large-Precat D (F on-obj X) (G on-obj X)
  natural-transformation_at_ = obj-natural-transformation-Large-Precat
```

Every functor comes equipped with an identity natural transformation.

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  where
  
  id-natural-transformation-Large-Precat :
    (F : functor-Large-Precat C D γF) → natural-transformation-Large-Precat F F
  obj-natural-transformation-Large-Precat
    (id-natural-transformation-Large-Precat F) X =
    id-hom-Large-Precat D
  coherence-square-natural-transformation-Large-Precat
    ( id-natural-transformation-Large-Precat F) f =
    ( left-unit-law-comp-hom-Large-Precat D (F on-mor f)) ∙
    ( inv (right-unit-law-comp-hom-Large-Precat D (F on-mor f)))
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
    {l : Level} (X : obj-Large-Precat C l) →
    is-iso-hom-Large-Precat D (F on-obj X) (G on-obj X) (natural-transformation η at X)
```

#### Homotopies of natural transformations

In Setω the identity type is not available. If it were, we would be able to characterize
the identity type of natural transformations from F to G as the type of homotopies of
natural transformations.

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  {F : functor-Large-Precat C D γF} {G : functor-Large-Precat C D γG}
  where

  htpy-natural-transformation-Large-Precat :
    (α β : natural-transformation-Large-Precat F G) → Setω
  htpy-natural-transformation-Large-Precat α β =
    {l : Level} (X : obj-Large-Precat C l) →
    Id ( obj-natural-transformation-Large-Precat α X)
       ( obj-natural-transformation-Large-Precat β X)

  refl-htpy-natural-transformation-Large-Precat :
    (α : natural-transformation-Large-Precat F G) →
    htpy-natural-transformation-Large-Precat α α
  refl-htpy-natural-transformation-Large-Precat α = refl-htpy

  concat-htpy-natural-transformation-Large-Precat :
    (α β γ : natural-transformation-Large-Precat F G) →
    htpy-natural-transformation-Large-Precat α β →
    htpy-natural-transformation-Large-Precat β γ →
    htpy-natural-transformation-Large-Precat α γ
  concat-htpy-natural-transformation-Large-Precat α β γ H K X =
    H X ∙ K X

  associative-concat-htpy-natural-transformation-Large-Precat :
    (α β γ δ : natural-transformation-Large-Precat F G)
    (H : htpy-natural-transformation-Large-Precat α β)
    (K : htpy-natural-transformation-Large-Precat β γ)
    (L : htpy-natural-transformation-Large-Precat γ δ) →
    {l : Level} (X : obj-Large-Precat C l) →
    Id ( concat-htpy-natural-transformation-Large-Precat α γ δ
         ( concat-htpy-natural-transformation-Large-Precat α β γ H K)
         ( L)
         ( X))
       ( concat-htpy-natural-transformation-Large-Precat α β δ
         ( H)
         ( concat-htpy-natural-transformation-Large-Precat β γ δ K L)
         ( X))
  associative-concat-htpy-natural-transformation-Large-Precat α β γ δ H K L X =
    assoc (H X) (K X) (L X)
```

#### Natural equivalences

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precat αC βC) (D : Large-Precat αD βD)
  where

  record equivalence-Large-Precat (γ-there γ-back : Level → Level) : Setω where
    constructor make-equivalence-Large-Precat
    field
      there-equivalence-Large-Precat : functor-Large-Precat C D γ-there
      back-equivalence-Large-Precat : functor-Large-Precat D C γ-back
      back-there-equivalence-Large-Precat :
        natural-isomorphism-Large-Precat
          (back-equivalence-Large-Precat ∘Functor there-equivalence-Large-Precat)
          (id-functor-Large-Precat)
      there-back-equivalence-Large-Precat :
        natural-isomorphism-Large-Precat
          (there-equivalence-Large-Precat ∘Functor back-equivalence-Large-Precat)
          (id-functor-Large-Precat)
```
