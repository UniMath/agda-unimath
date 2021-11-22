{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module foundations.15-image where

open import foundations.14-propositional-truncation public

--------------------------------------------------------------------------------

-- Section 15 The image of a map

--------------------------------------------------------------------------------

-- Section 15.1 The universal property of the image

-- Definition 15.1.1

-- Morphisms from f to g over X were introduced in Exercise 13.16

comp-hom-slice :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) →
  hom-slice g h → hom-slice f g → hom-slice f h
comp-hom-slice f g h j i =
  pair ( ( map-hom-slice g h j) ∘
         ( map-hom-slice f g i))
       ( ( triangle-hom-slice f g i) ∙h
         ( (triangle-hom-slice g h j) ·r (map-hom-slice f g i)))

id-hom-slice :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → hom-slice f f
id-hom-slice f = pair id refl-htpy

is-equiv-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → UU (l2 ⊔ l3)
is-equiv-hom-slice f g h = is-equiv (map-hom-slice f g h)

-- Definition 15.1.2 The universal property of the image

precomp-emb :
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} ( i : B ↪ X) (q : hom-slice f (map-emb i)) →
  {C : UU l4} ( j : C ↪ X) →
  hom-slice (map-emb i) (map-emb j) → hom-slice f (map-emb j)
precomp-emb f i q j r =
  pair
    ( ( map-hom-slice (map-emb i) (map-emb j) r) ∘
      ( map-hom-slice f (map-emb i) q))
    ( ( triangle-hom-slice f (map-emb i) q) ∙h
      ( ( triangle-hom-slice (map-emb i) (map-emb j) r) ·r
        ( map-hom-slice f (map-emb i) q)))

is-image :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
is-image l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) → is-equiv (precomp-emb f i q j)

-- Lemma 15.1.3

is-prop-hom-slice :
  { l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) → is-prop (hom-slice f (map-emb i))
is-prop-hom-slice {X = X} f i =
  is-prop-is-equiv
    ( (x : X) → fib f x → fib (map-emb i) x)
    ( fiberwise-hom-hom-slice f (map-emb i))
    ( is-equiv-fiberwise-hom-hom-slice f (map-emb i))
    ( is-prop-Π
      ( λ x → is-prop-Π
        ( λ p → is-prop-map-is-emb (is-emb-map-emb i) x)))

-- Proposition 15.1.4

-- Proposition 15.1.4 condition (ii)

is-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
is-image' l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) →
    hom-slice f (map-emb j) → hom-slice (map-emb i) (map-emb j)

{- We show that condition (ii) implies the universal property of the image
   inclusion. The other direction of the equivalence is trivial and never 
   needed. -}

is-image-is-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  is-image' l f i q → is-image l f i q
is-image-is-image' l f i q up' C j =
  is-equiv-is-prop
    ( is-prop-hom-slice (map-emb i) j)
    ( is-prop-hom-slice f j)
    ( up' C j)

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : {l : Level} → is-image l f i q)
  {C : UU l4} (j : C ↪ X) (r : hom-slice f (map-emb j))
  where
  
  universal-property-image :
    is-contr
      ( Σ ( hom-slice (map-emb i) (map-emb j))
          ( λ h →
            htpy-hom-slice f
              ( map-emb j)
              ( comp-hom-slice f (map-emb i) (map-emb j) h q)
              ( r)))
  universal-property-image =
    is-contr-equiv'
      ( fib (precomp-emb f i q j) r)
      ( equiv-tot
        ( λ h →
          equiv-htpy-eq-hom-slice f (map-emb j) (precomp-emb f i q j h) r))
      ( is-contr-map-is-equiv (H C j) r)

  hom-slice-universal-property-image : hom-slice (map-emb i) (map-emb j)
  hom-slice-universal-property-image =
    pr1 (center universal-property-image)

  map-hom-slice-universal-property-image : B → C
  map-hom-slice-universal-property-image =
    map-hom-slice (map-emb i) (map-emb j) hom-slice-universal-property-image

  triangle-hom-slice-universal-property-image :
    (map-emb i) ~ (map-emb j ∘ map-hom-slice-universal-property-image)
  triangle-hom-slice-universal-property-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb j)
      ( hom-slice-universal-property-image)

  htpy-hom-slice-universal-property-image :
    htpy-hom-slice f
      ( map-emb j)
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb j)
        ( hom-slice-universal-property-image)
        ( q))
      ( r)
  htpy-hom-slice-universal-property-image =
    pr2 (center universal-property-image)

  htpy-map-hom-slice-universal-property-image :
    map-hom-slice f
      ( map-emb j)
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb j)
        ( hom-slice-universal-property-image)
        ( q)) ~
    map-hom-slice f (map-emb j) r
  htpy-map-hom-slice-universal-property-image =
    pr1 htpy-hom-slice-universal-property-image

  tetrahedron-hom-slice-universal-property-image :
    ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
        ( ( triangle-hom-slice-universal-property-image) ·r
          ( map-hom-slice f (map-emb i) q))) ∙h
      ( map-emb j ·l htpy-map-hom-slice-universal-property-image)) ~
    ( triangle-hom-slice f (map-emb j) r)
  tetrahedron-hom-slice-universal-property-image =
    pr2 htpy-hom-slice-universal-property-image

--------------------------------------------------------------------------------

-- The existence of the image

-- Definition 15.1.5

module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where
    
  im : UU (l1 ⊔ l2)
  im = Σ X (λ x → type-trunc-Prop (fib f x))

  inclusion-im : im → X
  inclusion-im = pr1

  map-unit-im : A → im
  map-unit-im a = pair (f a) (unit-trunc-Prop (pair a refl))

  triangle-unit-im : f ~ (inclusion-im ∘ map-unit-im)
  triangle-unit-im a = refl

  unit-im : hom-slice f inclusion-im
  unit-im = pair map-unit-im triangle-unit-im

  hom-slice-im : hom-slice f inclusion-im
  hom-slice-im = pair map-unit-im triangle-unit-im

  -- We characterize the identity type of im f

  Eq-im : im → im → UU l1
  Eq-im x y = Id (pr1 x) (pr1 y)

  refl-Eq-im : (x : im) → Eq-im x x
  refl-Eq-im x = refl

  Eq-eq-im : (x y : im) → Id x y → Eq-im x y
  Eq-eq-im x .x refl = refl-Eq-im x

  is-contr-total-Eq-im :
    (x : im) → is-contr (Σ im (Eq-im x))
  is-contr-total-Eq-im x =
    is-contr-total-Eq-substructure
      ( is-contr-total-path (pr1 x))
      ( λ x → is-prop-type-trunc-Prop)
      ( pr1 x)
      ( refl)
      ( pr2 x)

  is-equiv-Eq-eq-im : (x y : im) → is-equiv (Eq-eq-im x y)
  is-equiv-Eq-eq-im x =
    fundamental-theorem-id x
      ( refl-Eq-im x)
      ( is-contr-total-Eq-im x)
      ( Eq-eq-im x)

  equiv-Eq-eq-im : (x y : im) → Id x y ≃ Eq-im x y
  equiv-Eq-eq-im x y = pair (Eq-eq-im x y) (is-equiv-Eq-eq-im x y)

  eq-Eq-im : (x y : im) → Eq-im x y → Id x y
  eq-Eq-im x y = map-inv-is-equiv (is-equiv-Eq-eq-im x y)

-- Proposition 15.1.6

is-emb-inclusion-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-emb (inclusion-im f)
is-emb-inclusion-im f =
  is-emb-pr1 (λ x → is-prop-type-trunc-Prop)

emb-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → im f ↪ X
emb-im f = pair (inclusion-im f) (is-emb-inclusion-im f)

is-injective-inclusion-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-injective (inclusion-im f)
is-injective-inclusion-im f =
  is-injective-is-emb (is-emb-inclusion-im f)

-- Theorem 15.1.7

fiberwise-map-is-image-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) →
  (x : X) → type-trunc-Prop (fib f x) → fib (map-emb m) x
fiberwise-map-is-image-im f m h x =
  map-universal-property-trunc-Prop
    { A = (fib f x)}
    ( fib-emb-Prop m x)
    ( λ t →
      pair ( map-hom-slice f (map-emb m) h (pr1 t))
           ( ( inv (triangle-hom-slice f (map-emb m) h (pr1 t))) ∙
             ( pr2 t)))

map-is-image-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) → im f → B
map-is-image-im f m h (pair x t) =
  pr1 (fiberwise-map-is-image-im f m h x t)

triangle-is-image-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) →
  inclusion-im f ~ ((map-emb m) ∘ (map-is-image-im f m h))
triangle-is-image-im f m h (pair x t) =
  inv (pr2 (fiberwise-map-is-image-im f m h x t))

is-image-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  {l : Level} → is-image l f (emb-im f) (hom-slice-im f)
is-image-im f {l} =
  is-image-is-image'
    l f (emb-im f) (hom-slice-im f)
    ( λ B m h →
      pair ( map-is-image-im f m h)
           ( triangle-is-image-im f m h))

{- We show some truncatedness results, so that we can use images as sets, and
   so on. -}

is-trunc-im :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A → X) →
  is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (im f)
is-trunc-im k f = is-trunc-emb k (emb-im f) 

is-prop-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-prop X → is-prop (im f)
is-prop-im = is-trunc-im neg-two-𝕋

is-set-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-set X → is-set (im f)
is-set-im = is-trunc-im neg-one-𝕋

is-1-type-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-1-type X → is-1-type (im f)
is-1-type-im = is-trunc-im zero-𝕋

im-Set :
  {l1 l2 : Level} {A : UU l2} (X : UU-Set l1) (f : A → type-Set X) →
  UU-Set (l1 ⊔ l2)
im-Set X f = pair (im f) (is-set-im f (is-set-type-Set X))

im-1-Type :
  {l1 l2 : Level} {A : UU l2} (X : UU-1-Type l1)
  (f : A → type-1-Type X) → UU-1-Type (l1 ⊔ l2)
im-1-Type X f = pair (im f) (is-1-type-im f (is-1-type-type-1-Type X))

--------------------------------------------------------------------------------

-- The uniqueness of the image

-- Proposition 15.1.8

is-equiv-hom-slice-emb :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A ↪ X) (g : B ↪ X) (h : hom-slice (map-emb f) (map-emb g)) →
  hom-slice (map-emb g) (map-emb f) →
  is-equiv-hom-slice (map-emb f) (map-emb g) h
is-equiv-hom-slice-emb f g h i =
  is-equiv-has-inverse
    ( map-hom-slice (map-emb g) (map-emb f) i)
    ( λ y →
      is-injective-emb g
      ( inv
        ( ( triangle-hom-slice
            ( map-emb g)
            ( map-emb f)
            ( i)
            ( y)) ∙
          ( triangle-hom-slice
            ( map-emb f)
            ( map-emb g)
            ( h)
            ( map-hom-slice (map-emb g) (map-emb f) i y)))))
    ( λ x →
      is-injective-emb f
      ( inv
        ( ( triangle-hom-slice (map-emb f) (map-emb g) h x) ∙
          ( triangle-hom-slice (map-emb g) (map-emb f) i
            ( map-hom-slice
              ( map-emb f)
              ( map-emb g)
              ( h)
              ( x))))))

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (h : hom-slice (map-emb i) (map-emb i'))
  -- (p : Id (comp-hom-slice f (map-emb i) (map-emb i') h q) q')
  where
  
  is-equiv-is-image-is-image :
    ({l : Level} → is-image l f i q) →
    ({l : Level} → is-image l f i' q') →
    is-equiv (map-hom-slice (map-emb i) (map-emb i') h)
  is-equiv-is-image-is-image up-i up-i' =
    is-equiv-hom-slice-emb i i' h (map-inv-is-equiv (up-i' B i) q)

  is-image-is-image-is-equiv :
    is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
    ({l : Level} → is-image l f i q) →
    ({l : Level} → is-image l f i' q')
  is-image-is-image-is-equiv is-equiv-h up-i {l} =
    is-image-is-image' l f i' q'
      ( λ C j r →
        comp-hom-slice
          ( map-emb i')
          ( map-emb i)
          ( map-emb j)
          ( map-inv-is-equiv (up-i C j) r)
          ( pair
            ( map-inv-is-equiv is-equiv-h)
            ( triangle-section
              ( map-emb i)
              ( map-emb i')
              ( map-hom-slice (map-emb i) (map-emb i') h)
              ( triangle-hom-slice (map-emb i) (map-emb i') h)
              ( pair ( map-inv-is-equiv is-equiv-h)
                     ( issec-map-inv-is-equiv is-equiv-h)))))

  is-image-is-equiv-is-image :
    ({l : Level} → is-image l f i' q') →
    is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
    ({l : Level} → is-image l f i q)
  is-image-is-equiv-is-image up-i' is-equiv-h {l} =
    is-image-is-image' l f i q
      ( λ C j r →
        comp-hom-slice
          ( map-emb i)
          ( map-emb i')
          ( map-emb j)
          ( map-inv-is-equiv (up-i' C j) r)
          ( h))

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (Hi : {l : Level} → is-image l f i q)
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (Hi' : {l : Level} → is-image l f i' q')
  where

  uniqueness-image :
    is-contr
      ( Σ ( equiv-slice (map-emb i) (map-emb i'))
          ( λ e →
            htpy-hom-slice f
              ( map-emb i')
              ( comp-hom-slice f
                ( map-emb i)
                ( map-emb i')
                ( hom-equiv-slice (map-emb i) (map-emb i') e)
                ( q))
              ( q')))
  uniqueness-image =
    is-contr-equiv
      ( Σ ( Σ ( hom-slice (map-emb i) (map-emb i'))
              ( λ h →
                htpy-hom-slice f
                  ( map-emb i')
                  ( comp-hom-slice f (map-emb i) (map-emb i') h q)
                  ( q')))
          ( λ h → is-equiv (pr1 (pr1 h))))
      ( ( equiv-right-swap-Σ) ∘e
        ( equiv-Σ
          ( λ h →
            htpy-hom-slice f
              ( map-emb i')
              ( comp-hom-slice f (map-emb i) (map-emb i') (pr1 h) q)
              ( q'))
          ( equiv-right-swap-Σ)
          ( λ { (pair (pair e E) H) → equiv-id})))
      ( is-contr-equiv
        ( is-equiv
          ( map-hom-slice-universal-property-image f i q Hi i' q'))
        ( left-unit-law-Σ-is-contr
          ( universal-property-image f i q Hi i' q')
          ( center (universal-property-image f i q Hi i' q')))
        ( is-proof-irrelevant-is-prop
          ( is-subtype-is-equiv
            ( map-hom-slice-universal-property-image f i q Hi i' q'))
          ( is-equiv-is-image-is-image f i q i' q'
            ( hom-slice-universal-property-image f i q Hi i' q')
            ( Hi)
            ( Hi'))))

  equiv-slice-uniqueness-image : equiv-slice (map-emb i) (map-emb i')
  equiv-slice-uniqueness-image =
    pr1 (center uniqueness-image)

  hom-equiv-slice-uniqueness-image : hom-slice (map-emb i) (map-emb i')
  hom-equiv-slice-uniqueness-image =
    hom-equiv-slice (map-emb i) (map-emb i') (equiv-slice-uniqueness-image)

  map-hom-equiv-slice-uniqueness-image : B → B'
  map-hom-equiv-slice-uniqueness-image =
    map-hom-slice (map-emb i) (map-emb i') (hom-equiv-slice-uniqueness-image)

  is-equiv-map-hom-equiv-slice-uniqueness-image :
    is-equiv map-hom-equiv-slice-uniqueness-image
  is-equiv-map-hom-equiv-slice-uniqueness-image =
    is-equiv-map-equiv (pr1 equiv-slice-uniqueness-image)

  equiv-equiv-slice-uniqueness-image : B ≃ B'
  equiv-equiv-slice-uniqueness-image =
    pair map-hom-equiv-slice-uniqueness-image
         is-equiv-map-hom-equiv-slice-uniqueness-image

  triangle-hom-equiv-slice-uniqueness-image :
    (map-emb i) ~ (map-emb i' ∘ map-hom-equiv-slice-uniqueness-image)
  triangle-hom-equiv-slice-uniqueness-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb i')
      ( hom-equiv-slice-uniqueness-image)

  htpy-equiv-slice-uniqueness-image :
    htpy-hom-slice f
      ( map-emb i')
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb i')
        ( hom-equiv-slice-uniqueness-image)
        ( q))
      ( q')
  htpy-equiv-slice-uniqueness-image =
    pr2 (center uniqueness-image)

  htpy-map-hom-equiv-slice-uniqueness-image :
    ( map-hom-equiv-slice-uniqueness-image ∘ map-hom-slice f (map-emb i) q) ~
    ( map-hom-slice f (map-emb i') q')
  htpy-map-hom-equiv-slice-uniqueness-image =
    pr1 htpy-equiv-slice-uniqueness-image

  tetrahedron-hom-equiv-slice-uniqueness-image :
    ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-image) ·r
          ( map-hom-slice f (map-emb i) q))) ∙h
      ( map-emb i' ·l htpy-map-hom-equiv-slice-uniqueness-image)) ~
    ( triangle-hom-slice f (map-emb i') q')
  tetrahedron-hom-equiv-slice-uniqueness-image =
    pr2 htpy-equiv-slice-uniqueness-image

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : {l : Level} → is-image l f i q)
  where

  uniqueness-im :
    is-contr
      ( Σ ( equiv-slice (inclusion-im f) (map-emb i))
          ( λ e →
            htpy-hom-slice f
              ( map-emb i)
              ( comp-hom-slice f
                ( inclusion-im f)
                ( map-emb i)
                ( hom-equiv-slice (inclusion-im f) (map-emb i) e)
                ( hom-slice-im f))
              ( q)))
  uniqueness-im =
    uniqueness-image f (emb-im f) (hom-slice-im f) (is-image-im f) i q H

  equiv-slice-uniqueness-im : equiv-slice (inclusion-im f) (map-emb i)
  equiv-slice-uniqueness-im =
    pr1 (center uniqueness-im)

  hom-equiv-slice-uniqueness-im : hom-slice (inclusion-im f) (map-emb i)
  hom-equiv-slice-uniqueness-im =
    hom-equiv-slice (inclusion-im f) (map-emb i) equiv-slice-uniqueness-im

  map-hom-equiv-slice-uniqueness-im : im f → B
  map-hom-equiv-slice-uniqueness-im =
    map-hom-slice (inclusion-im f) (map-emb i) hom-equiv-slice-uniqueness-im

  is-equiv-map-hom-equiv-slice-uniqueness-im :
    is-equiv map-hom-equiv-slice-uniqueness-im
  is-equiv-map-hom-equiv-slice-uniqueness-im =
    is-equiv-map-equiv (pr1 equiv-slice-uniqueness-im)

  equiv-equiv-slice-uniqueness-im : im f ≃ B
  equiv-equiv-slice-uniqueness-im =
    pair map-hom-equiv-slice-uniqueness-im
         is-equiv-map-hom-equiv-slice-uniqueness-im

  triangle-hom-equiv-slice-uniqueness-im :
    (inclusion-im f) ~ (map-emb i ∘ map-hom-equiv-slice-uniqueness-im)
  triangle-hom-equiv-slice-uniqueness-im =
    triangle-hom-slice
      ( inclusion-im f)
      ( map-emb i)
      ( hom-equiv-slice-uniqueness-im)

  htpy-equiv-slice-uniqueness-im :
    htpy-hom-slice f
      ( map-emb i)
      ( comp-hom-slice f
        ( inclusion-im f)
        ( map-emb i)
        ( hom-equiv-slice-uniqueness-im)
        ( hom-slice-im f))
      ( q)
  htpy-equiv-slice-uniqueness-im =
    pr2 (center uniqueness-im)

  htpy-map-hom-equiv-slice-uniqueness-im :
    ( ( map-hom-equiv-slice-uniqueness-im) ∘
      ( map-hom-slice f (inclusion-im f) (hom-slice-im f))) ~
    ( map-hom-slice f (map-emb i) q)
  htpy-map-hom-equiv-slice-uniqueness-im =
    pr1 htpy-equiv-slice-uniqueness-im

  tetrahedron-hom-equiv-slice-uniqueness-im :
    ( ( ( triangle-hom-slice f (inclusion-im f) (hom-slice-im f)) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-im) ·r
          ( map-hom-slice f (inclusion-im f) (hom-slice-im f)))) ∙h
      ( map-emb i ·l htpy-map-hom-equiv-slice-uniqueness-im)) ~
    ( triangle-hom-slice f (map-emb i) q)
  tetrahedron-hom-equiv-slice-uniqueness-im =
    pr2 htpy-equiv-slice-uniqueness-im
    
--------------------------------------------------------------------------------

-- Section 15.2 Surjective maps

-- Definition 15.2.1

is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective {B = B} f = (y : B) → type-trunc-Prop (fib f y)

-- Example 15.2.2

is-surjective-has-section :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  sec f → is-surjective f
is-surjective-has-section (pair g G) b = unit-trunc-Prop (pair (g b) (G b))

is-split-epimorphism :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-split-epimorphism f = sec f

is-surjective-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-surjective f
is-surjective-is-equiv H = is-surjective-has-section (pr1 H)

-- Proposition 15.2.3

dependent-universal-property-surj :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  UU ((lsuc l) ⊔ l1 ⊔ l2)
dependent-universal-property-surj l {B = B} f =
  (P : B → UU-Prop l) →
    is-equiv (λ (h : (b : B) → type-Prop (P b)) x → h (f x))

is-surjective-dependent-universal-property-surj :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ({l : Level} → dependent-universal-property-surj l f) →
  is-surjective f
is-surjective-dependent-universal-property-surj f dup-surj-f =
  map-inv-is-equiv
    ( dup-surj-f (λ b → trunc-Prop (fib f b)))
    ( λ x → unit-trunc-Prop (pair x refl))

square-dependent-universal-property-surj :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (P : B → UU-Prop l3) →
  ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
  ( ( λ h x → h (f x) (pair x refl)) ∘
    ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))))
square-dependent-universal-property-surj f P = refl-htpy

dependent-universal-property-surj-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f →
  ({l : Level} → dependent-universal-property-surj l f)
dependent-universal-property-surj-is-surjective f is-surj-f P =
  is-equiv-comp'
    ( λ h x → h (f x) (pair x refl))
    ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y)))
    ( is-equiv-comp'
      ( λ h y → (h y) ∘ unit-trunc-Prop)
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))
      ( is-equiv-map-Π
        ( λ y p z → p)
        ( λ y →
          is-equiv-diagonal-is-contr
            ( is-proof-irrelevant-is-prop
              ( is-prop-type-trunc-Prop)
              ( is-surj-f y))
            ( type-Prop (P y))))
      ( is-equiv-map-Π
        ( λ b g → g ∘ unit-trunc-Prop)
        ( λ b → is-propositional-truncation-trunc-Prop (fib f b) (P b))))
    ( is-equiv-map-reduce-Π-fib f ( λ y z → type-Prop (P y)))

equiv-dependent-universal-property-surj-is-surjective :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f → (C : B → UU-Prop l) →
  ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (f a)))
equiv-dependent-universal-property-surj-is-surjective f H C =
  pair
    ( λ h x → h (f x))
    ( dependent-universal-property-surj-is-surjective f H C)

-- Corollary 15.2.4

is-surjective-is-propositional-truncation :
  {l1 l2 : Level} {A : UU l1} {P : UU-Prop l2} (f : A → type-Prop P) →
    ({l : Level} → dependent-universal-property-propositional-truncation l P f) → is-surjective f
is-surjective-is-propositional-truncation f duppt-f =
  is-surjective-dependent-universal-property-surj f duppt-f

is-propsitional-truncation-is-surjective :
  {l1 l2 : Level} {A : UU l1} {P : UU-Prop l2} (f : A → type-Prop P) →
    is-surjective f → {l : Level} → dependent-universal-property-propositional-truncation l P f
is-propsitional-truncation-is-surjective f is-surj-f =
  dependent-universal-property-surj-is-surjective f is-surj-f

-- Theorem 15.2.5

-- Theorem 15.2.5 (i) implies (ii)

is-surjective-is-image :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  ({l : Level} → is-image l f i q) →
  is-surjective (map-hom-slice f (map-emb i) q)
is-surjective-is-image {A = A} {B} {X} f i q up-i b =
  apply-universal-property-trunc-Prop β
    ( trunc-Prop (fib (map-hom-slice f (map-emb i) q) b))
    ( γ)
  where
  g : Σ B (λ b → type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) b)) → X
  g = map-emb i ∘ pr1
  is-emb-g : is-emb g
  is-emb-g = is-emb-comp' (map-emb i) pr1
    ( is-emb-map-emb i)
    ( is-emb-pr1 (λ x → is-prop-type-trunc-Prop))
  α : hom-slice (map-emb i) g
  α = map-inv-is-equiv
        ( up-i
          ( Σ B ( λ b →
                  type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) b)))
          ( pair g is-emb-g))
        ( pair (map-unit-im (pr1 q)) (pr2 q))
  β : type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)))
  β = pr2 (pr1 α b)
  γ : fib (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)) →
      type-Prop (trunc-Prop (fib (pr1 q) b))
  γ (pair a p) =
    unit-trunc-Prop
      ( pair a (p ∙ inv (is-injective-is-emb (is-emb-map-emb i) (pr2 α b))))

is-surjective-map-unit-im :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective (map-unit-im f)
is-surjective-map-unit-im f (pair y z) =
  apply-universal-property-trunc-Prop z
    ( trunc-Prop (fib (map-unit-im f) (pair y z)))
    ( α)
  where
  α : fib f y → type-Prop (trunc-Prop (fib (map-unit-im f) (pair y z)))
  α (pair x p) =
    unit-trunc-Prop (pair x (eq-subtype (λ z → is-prop-type-trunc-Prop) p))

-- Theorem 15.2.5 (ii) implies (i)

is-image-is-surjective' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  is-surjective (map-hom-slice f (map-emb i) q) →
  ({l : Level} → is-image' l f i q)
is-image-is-surjective' f i q H B' m =
  map-equiv
    ( ( equiv-hom-slice-fiberwise-hom (map-emb i) (map-emb m)) ∘e
      ( ( inv-equiv (reduce-Π-fib (map-emb i) (fib (map-emb m)))) ∘e
        ( inv-equiv
          ( equiv-dependent-universal-property-surj-is-surjective
            ( pr1 q)
            ( H)
            ( λ b →
              pair ( fib (map-emb m) (pr1 i b))
                   ( is-prop-map-emb m (pr1 i b)))) ∘e
          ( ( equiv-map-Π (λ a → equiv-tr (fib (map-emb m)) (pr2 q a))) ∘e
            ( ( reduce-Π-fib f (fib (map-emb m))) ∘e
              ( equiv-fiberwise-hom-hom-slice f (map-emb m)))))))

is-image-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  is-surjective (map-hom-slice f (map-emb i) q) →
  ({l : Level} → is-image l f i q)
is-image-is-surjective f i q H {l} =
  is-image-is-image' l f i q
    ( is-image-is-surjective' f i q H)

--------------------------------------------------------------------------------

-- Section 14.6 Cantor's diagonal argument

-- Definition 14.6.1

-- Theorem 14.6.2

map-cantor :
  {l1 l2 : Level} (X : UU l1) (f : X → (X → UU-Prop l2)) → (X → UU-Prop l2)
map-cantor X f x = neg-Prop (f x x)

iff-eq :
  {l1 : Level} {P Q : UU-Prop l1} → Id P Q → P ⇔ Q
iff-eq refl = pair id id

no-fixed-points-neg-Prop :
  {l1 : Level} (P : UU-Prop l1) → ¬ (P ⇔ neg-Prop P)
no-fixed-points-neg-Prop P = no-fixed-points-neg (type-Prop P)

not-in-image-map-cantor :
  {l1 l2 : Level} (X : UU l1) (f : X → (X → UU-Prop l2)) →
  ( t : fib f (map-cantor X f)) → empty
not-in-image-map-cantor X f (pair x α) =
  no-fixed-points-neg-Prop (f x x) (iff-eq (htpy-eq α x))

cantor : {l1 l2 : Level} (X : UU l1) (f : X → (X → UU-Prop l2)) →
  ¬ (is-surjective f)
cantor X f H =
  ( apply-universal-property-trunc-Prop
    ( H (map-cantor X f))
    ( empty-Prop)
    ( not-in-image-map-cantor X f))

--------------------------------------------------------------------------------

-- Exercise 15.3

is-equiv-is-emb-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → is-emb f → is-equiv f
is-equiv-is-emb-is-surjective {f = f} H K =
  is-equiv-is-contr-map
    ( λ y →
      is-proof-irrelevant-is-prop
        ( is-prop-map-is-emb K y)
        ( apply-universal-property-trunc-Prop
          ( H y)
          ( fib-emb-Prop (pair f K) y)
          ( id)))

-- Exercise 15.4

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-surjective-comp :
    is-surjective g → is-surjective h → is-surjective f
  is-surjective-comp Sg Sh x =
    apply-universal-property-trunc-Prop
      ( Sg x)
      ( trunc-Prop (fib f x))
      ( λ { (pair b refl) →
            apply-universal-property-trunc-Prop
              ( Sh b)
              ( trunc-Prop (fib f (g b)))
              ( λ { (pair a refl) →
                unit-trunc-Prop (pair a (H a))})})

  is-surjective-left-factor :
    is-surjective f → is-surjective g
  is-surjective-left-factor Sf x =
    apply-universal-property-trunc-Prop
      ( Sf x)
      ( trunc-Prop (fib g x))
      ( λ { (pair a refl) →
            unit-trunc-Prop (pair (h a) (inv (H a)))})

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {g : B → X}
  where

  is-surjective-comp' :
    {h : A → B} → is-surjective g → is-surjective h → is-surjective (g ∘ h)
  is-surjective-comp' {h} =
    is-surjective-comp (g ∘ h) g h refl-htpy

  is-surjective-left-factor' :
    (h : A → B) → is-surjective (g ∘ h) → is-surjective g
  is-surjective-left-factor' h =
    is-surjective-left-factor (g ∘ h) g h refl-htpy
            
-- Exercise 15.5

fixed-point-theorem-Lawvere :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → A → B} →
  is-surjective f → (h : B → B) → ∃ (λ b → Id (h b) b)
fixed-point-theorem-Lawvere {A = A} {B} {f} H h =
  apply-universal-property-trunc-Prop
    ( H g)
    ( ∃-Prop (λ b → Id (h b) b))
    ( λ p → intro-∃ (f (pr1 p) (pr1 p)) (inv (htpy-eq (pr2 p) (pr1 p))))
  where
  g : A → B
  g a = h (f a a)

--------------------------------------------------------------------------------

-- Moved to end of file

-- Example 14.4.5

is-image-has-section :
  (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  sec f → is-image l f emb-id (pair f refl-htpy)
is-image-has-section l f (pair g H) =
  is-image-is-image'
    l f emb-id (pair f refl-htpy)
    ( λ B m h → pair ((pr1 h) ∘ g) ( λ x → (inv (H x)) ∙ (pr2 h (g x))))

is-image-is-emb :
  (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  (H : is-emb f) → is-image l f (pair f H) (pair id refl-htpy)
is-image-is-emb l f H =
  is-image-is-image'
    l f (pair f H) (pair id refl-htpy)
    ( λ B m h → h)

-- Example 14.4.6

{- We show that a map A → P into a proposition P is a propositional truncation
   if and only if P is the image of A in 1. -}
