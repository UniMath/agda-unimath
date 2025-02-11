# Functoriality of coproduct types

```agda
module foundation.functoriality-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.negated-equality
open import foundation.propositional-truncations
open import foundation.retractions
open import foundation.structure-identity-principle
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Any two maps `f : A → B` and `g : C → D` induce a map
`map-coproduct f g : coproduct A B → coproduct C D`.

## Definitions

### The functorial action of the coproduct operation

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

  map-coproduct : (A → A') → (B → B') → A + B → A' + B'
  map-coproduct f g (inl x) = inl (f x)
  map-coproduct f g (inr y) = inr (g y)
```

## Properties

### Functoriality of coproducts preserves identity maps

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  id-map-coproduct : (map-coproduct (id {A = A}) (id {A = B})) ~ id
  id-map-coproduct (inl x) = refl
  id-map-coproduct (inr x) = refl
```

### Functoriality of coproducts preserves composition

```agda
module _
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'')
  where

  preserves-comp-map-coproduct :
    map-coproduct (f' ∘ f) (g' ∘ g) ~ map-coproduct f' g' ∘ map-coproduct f g
  preserves-comp-map-coproduct (inl x) = refl
  preserves-comp-map-coproduct (inr y) = refl
```

### Functoriality of coproducts preserves homotopies

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g')
  where

  htpy-map-coproduct : map-coproduct f g ~ map-coproduct f' g'
  htpy-map-coproduct (inl x) = ap inl (H x)
  htpy-map-coproduct (inr y) = ap inr (K y)
```

### The fibers of `map-coproduct`

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B)
  where

  fiber-map-coproduct-inl-fiber :
    (x : A) → fiber f x → fiber (map-coproduct f g) (inl x)
  pr1 (fiber-map-coproduct-inl-fiber x (a' , p)) = inl a'
  pr2 (fiber-map-coproduct-inl-fiber x (a' , p)) = ap inl p

  fiber-fiber-map-coproduct-inl :
    (x : A) → fiber (map-coproduct f g) (inl x) → fiber f x
  pr1 (fiber-fiber-map-coproduct-inl x (inl a' , p)) = a'
  pr2 (fiber-fiber-map-coproduct-inl x (inl a' , p)) =
    map-compute-eq-coproduct-inl-inl (f a') x p
  fiber-fiber-map-coproduct-inl x (inr b' , p) =
    ex-falso (is-empty-eq-coproduct-inr-inl (g b') x p)

  abstract
    is-section-fiber-fiber-map-coproduct-inl :
      (x : A) →
      fiber-map-coproduct-inl-fiber x ∘ fiber-fiber-map-coproduct-inl x ~ id
    is-section-fiber-fiber-map-coproduct-inl .(f a') (inl a' , refl) = refl
    is-section-fiber-fiber-map-coproduct-inl x (inr b' , p) =
      ex-falso (is-empty-eq-coproduct-inr-inl (g b') x p)

  abstract
    is-retraction-fiber-fiber-map-coproduct-inl :
      (x : A) →
      fiber-fiber-map-coproduct-inl x ∘ fiber-map-coproduct-inl-fiber x ~ id
    is-retraction-fiber-fiber-map-coproduct-inl .(f a') (a' , refl) = refl

  abstract
    is-equiv-fiber-map-coproduct-inl-fiber :
      (x : A) → is-equiv (fiber-map-coproduct-inl-fiber x)
    is-equiv-fiber-map-coproduct-inl-fiber x =
      is-equiv-is-invertible
        ( fiber-fiber-map-coproduct-inl x)
        ( is-section-fiber-fiber-map-coproduct-inl x)
        ( is-retraction-fiber-fiber-map-coproduct-inl x)

  compute-fiber-inl-map-coproduct :
    (x : A) → fiber f x ≃ fiber (map-coproduct f g) (inl x)
  compute-fiber-inl-map-coproduct x =
    ( fiber-map-coproduct-inl-fiber x ,
      is-equiv-fiber-map-coproduct-inl-fiber x)

  fiber-map-coproduct-inr-fiber :
    (y : B) → fiber g y → fiber (map-coproduct f g) (inr y)
  pr1 (fiber-map-coproduct-inr-fiber y (b' , p)) = inr b'
  pr2 (fiber-map-coproduct-inr-fiber y (b' , p)) = ap inr p

  fiber-fiber-map-coproduct-inr :
    (y : B) → fiber (map-coproduct f g) (inr y) → fiber g y
  fiber-fiber-map-coproduct-inr y (inl a' , p) =
    ex-falso (is-empty-eq-coproduct-inl-inr (f a') y p)
  pr1 (fiber-fiber-map-coproduct-inr y (inr b' , p)) = b'
  pr2 (fiber-fiber-map-coproduct-inr y (inr b' , p)) =
    map-compute-eq-coproduct-inr-inr (g b') y p

  abstract
    is-section-fiber-fiber-map-coproduct-inr :
      (y : B) →
      (fiber-map-coproduct-inr-fiber y ∘ fiber-fiber-map-coproduct-inr y) ~ id
    is-section-fiber-fiber-map-coproduct-inr .(g b') (inr b' , refl) = refl
    is-section-fiber-fiber-map-coproduct-inr y (inl a' , p) =
      ex-falso (is-empty-eq-coproduct-inl-inr (f a') y p)

  abstract
    is-retraction-fiber-fiber-map-coproduct-inr :
      (y : B) →
      (fiber-fiber-map-coproduct-inr y ∘ fiber-map-coproduct-inr-fiber y) ~ id
    is-retraction-fiber-fiber-map-coproduct-inr .(g b') (b' , refl) = refl

  abstract
    is-equiv-fiber-map-coproduct-inr-fiber :
      (y : B) → is-equiv (fiber-map-coproduct-inr-fiber y)
    is-equiv-fiber-map-coproduct-inr-fiber y =
      is-equiv-is-invertible
        ( fiber-fiber-map-coproduct-inr y)
        ( is-section-fiber-fiber-map-coproduct-inr y)
        ( is-retraction-fiber-fiber-map-coproduct-inr y)

  compute-fiber-inr-map-coproduct :
    (y : B) → fiber g y ≃ fiber (map-coproduct f g) (inr y)
  compute-fiber-inr-map-coproduct y =
    ( fiber-map-coproduct-inr-fiber y ,
      is-equiv-fiber-map-coproduct-inr-fiber y)
```

### Functoriality of coproducts preserves equivalences

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

  map-equiv-coproduct : A ≃ A' → B ≃ B' → A + B → A' + B'
  map-equiv-coproduct f g = map-coproduct (map-equiv f) (map-equiv g)

  map-inv-equiv-coproduct : A ≃ A' → B ≃ B' → A' + B' → A + B
  map-inv-equiv-coproduct f g =
    map-coproduct (map-inv-equiv f) (map-inv-equiv g)

  is-section-map-inv-equiv-coproduct :
    (f : A ≃ A') (g : B ≃ B') →
    is-section
      ( map-equiv-coproduct f g)
      ( map-inv-equiv-coproduct f g)
  is-section-map-inv-equiv-coproduct f g =
    ( inv-htpy
      ( preserves-comp-map-coproduct
        ( map-inv-equiv f)
        ( map-equiv f)
        ( map-inv-equiv g)
        ( map-equiv g))) ∙h
    ( htpy-map-coproduct
      ( is-section-map-inv-equiv f)
      ( is-section-map-inv-equiv g)) ∙h
    ( id-map-coproduct A' B')

  is-retraction-map-inv-equiv-coproduct :
    (f : A ≃ A') (g : B ≃ B') →
    is-retraction
      ( map-equiv-coproduct f g)
      ( map-inv-equiv-coproduct f g)
  is-retraction-map-inv-equiv-coproduct f g =
    ( inv-htpy
      ( preserves-comp-map-coproduct
        ( map-equiv f)
        ( map-inv-equiv f)
        ( map-equiv g)
        ( map-inv-equiv g))) ∙h
    ( htpy-map-coproduct
      ( is-retraction-map-inv-equiv f)
      ( is-retraction-map-inv-equiv g)) ∙h
    ( id-map-coproduct A B)

  is-equiv-map-coproduct :
    {f : A → A'} {g : B → B'} →
    is-equiv f → is-equiv g → is-equiv (map-coproduct f g)
  is-equiv-map-coproduct {f} {g} H K =
    is-equiv-is-invertible
      ( map-coproduct (map-inv-is-equiv H) (map-inv-is-equiv K))
      ( is-section-map-inv-equiv-coproduct (f , H) (g , K))
      ( is-retraction-map-inv-equiv-coproduct (f , H) (g , K))

  equiv-coproduct : A ≃ A' → B ≃ B' → (A + B) ≃ (A' + B')
  equiv-coproduct e e' =
    ( map-equiv-coproduct e e' ,
      is-equiv-map-coproduct (is-equiv-map-equiv e) (is-equiv-map-equiv e'))
```

### The functorial action of coproducts preserves retractions

```agda
module _
  {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f : A → B} {f' : A' → B'} (r : retraction f) (r' : retraction f')
  where

  map-retraction-map-coproduct : B + B' → A + A'
  map-retraction-map-coproduct =
    map-coproduct (map-retraction f r) (map-retraction f' r')

  is-retraction-retraction-map-coproduct :
    is-retraction (map-coproduct f f') map-retraction-map-coproduct
  is-retraction-retraction-map-coproduct =
    ( inv-htpy
      ( preserves-comp-map-coproduct
        ( f)
        ( map-retraction f r)
        ( f')
        ( map-retraction f' r'))) ∙h
    ( htpy-map-coproduct
      ( is-retraction-map-retraction f r)
      ( is-retraction-map-retraction f' r')) ∙h
    ( id-map-coproduct A A')

  retraction-map-coproduct : retraction (map-coproduct f f')
  retraction-map-coproduct =
    ( map-retraction-map-coproduct , is-retraction-retraction-map-coproduct)
```

### Functoriality of coproducts preserves embeddings

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

abstract
  is-emb-map-coproduct :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    {f : A → B} {g : X → Y} →
    is-emb f → is-emb g → is-emb (map-coproduct f g)
  is-emb-map-coproduct {f = f} {g} F G (inl x) (inl y) =
    is-equiv-left-is-equiv-right-square
      ( ap (map-coproduct f g))
      ( ap f)
      ( map-compute-eq-coproduct-inl-inl x y)
      ( map-compute-eq-coproduct-inl-inl (f x) (f y))
      ( λ where refl → refl)
      ( is-equiv-map-compute-eq-coproduct-inl-inl x y)
      ( is-equiv-map-compute-eq-coproduct-inl-inl (f x) (f y))
      ( F x y)
  is-emb-map-coproduct {f = f} {g} F G (inl x) (inr y) =
    is-equiv-is-empty
      ( ap (map-coproduct f g))
      ( is-empty-eq-coproduct-inl-inr (f x) (g y))
  is-emb-map-coproduct {f = f} {g} F G (inr x) (inl y) =
    is-equiv-is-empty
      ( ap (map-coproduct f g))
      ( is-empty-eq-coproduct-inr-inl (g x) (f y))
  is-emb-map-coproduct {f = f} {g} F G (inr x) (inr y) =
    is-equiv-left-is-equiv-right-square
      ( ap (map-coproduct f g))
      ( ap g)
      ( map-compute-eq-coproduct-inr-inr x y)
      ( map-compute-eq-coproduct-inr-inr (g x) (g y))
      ( λ where refl → refl)
      ( is-equiv-map-compute-eq-coproduct-inr-inr x y)
      ( is-equiv-map-compute-eq-coproduct-inr-inr (g x) (g y))
      ( G x y)
```

### Functoriality of coproducts preserves surjections

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

  abstract
    is-surjective-map-coproduct :
      {f : A → A'} {g : B → B'} →
      is-surjective f → is-surjective g →
      is-surjective (map-coproduct f g)
    is-surjective-map-coproduct s s' (inl x) =
      apply-universal-property-trunc-Prop (s x)
        ( trunc-Prop (fiber (map-coproduct _ _) (inl x)))
        ( λ (a , p) → unit-trunc-Prop (inl a , ap inl p))
    is-surjective-map-coproduct s s' (inr x) =
      apply-universal-property-trunc-Prop (s' x)
        ( trunc-Prop (fiber (map-coproduct _ _) (inr x)))
        ( λ (a , p) → unit-trunc-Prop (inr a , ap inr p))
```

### For any two maps `f : A → B` and `g : C → D`, there is at most one pair of maps `f' : A → B` and `g' : C → D` such that `f' + g' = f + g`

```agda
is-contr-fiber-map-coproduct :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) →
  is-contr
    ( fiber
      ( λ (fg' : (A → B) × (C → D)) → map-coproduct (pr1 fg') (pr2 fg'))
      ( map-coproduct f g))
is-contr-fiber-map-coproduct {A = A} {B} {C} {D} f g =
  is-contr-equiv
    ( Σ ( (A → B) × (C → D))
        ( λ fg' →
          ((a : A) → pr1 fg' a ＝ f a) × ((c : C) → pr2 fg' c ＝ g c)))
    ( equiv-tot
      ( λ fg' →
        ( equiv-product
          ( equiv-Π-equiv-family
            ( λ a → compute-eq-coproduct-inl-inl (pr1 fg' a) (f a)))
          ( equiv-Π-equiv-family
            ( λ c → compute-eq-coproduct-inr-inr (pr2 fg' c) (g c)))) ∘e
        ( equiv-dependent-universal-property-coproduct
          ( λ x → map-coproduct (pr1 fg') (pr2 fg') x ＝ map-coproduct f g x)) ∘e
        ( equiv-funext)))
    ( is-torsorial-Eq-structure
      ( is-torsorial-htpy' f)
      ( f , refl-htpy)
      ( is-torsorial-htpy' g))
```

### For any equivalence `f : A + B ≃ A + B` and `g : B ≃ B` such that `f` and `g` coincide on `B`, we construct an `h : A ≃ A` such that `htpy-equiv (equiv-coproduct h d) f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-coproduct-induce-equiv-disjoint :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y : B) → map-equiv f (inl x) ≠ inr y
  equiv-coproduct-induce-equiv-disjoint f g p x y q =
    neq-inr-inl
      ( is-injective-equiv f
        ( ( p (map-equiv (inv-equiv g) y) ∙
          ( ( ap (λ z → inr (map-equiv z y)) (right-inverse-law-equiv g)) ∙
            ( inv q)))))

  inv-commutative-square-inr :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b)) →
    (b : B) → map-inv-equiv f (inr b) ＝ inr (map-inv-equiv g b)
  inv-commutative-square-inr f g p b =
    is-injective-equiv f
      ( ( ap (λ z → map-equiv z (inr b)) (right-inverse-law-equiv f)) ∙
        ( inv (ap (λ z → inr (map-equiv z b)) (right-inverse-law-equiv g))) ∙
        ( inv (p (map-inv-equiv g b))))

  cases-retraction-equiv-coproduct :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y : A + B) → map-equiv f (inl x) ＝ y → A
  cases-retraction-equiv-coproduct f g p x (inl y) q = y
  cases-retraction-equiv-coproduct f g p x (inr y) q =
    ex-falso (equiv-coproduct-induce-equiv-disjoint f g p x y q)

  inv-cases-retraction-equiv-coproduct :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y : A + B) → map-inv-equiv f (inl x) ＝ y → A
  inv-cases-retraction-equiv-coproduct f g p =
    cases-retraction-equiv-coproduct
      ( inv-equiv f)
      ( inv-equiv g)
      ( inv-commutative-square-inr f g p)

  retraction-cases-retraction-equiv-coproduct :
    ( f : (A + B) ≃ (A + B)) (g : B ≃ B)
    ( p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    ( x : A) (y z : A + B) (q : map-equiv f (inl x) ＝ y)
    ( r :
      ( map-inv-equiv f (inl (cases-retraction-equiv-coproduct f g p x y q))) ＝
      ( z)) →
    ( inv-cases-retraction-equiv-coproduct f g p
      ( cases-retraction-equiv-coproduct f g p x y q) z r) ＝
    ( x)
  retraction-cases-retraction-equiv-coproduct f g p x (inl y) (inl z) q r =
    is-injective-inl
      ( ( inv r) ∙
        ( ( ap (map-inv-equiv f) (inv q)) ∙
          ( ap (λ w → map-equiv w (inl x)) (left-inverse-law-equiv f))))
  retraction-cases-retraction-equiv-coproduct f g p x (inl y) (inr z) q r =
    ex-falso
      ( equiv-coproduct-induce-equiv-disjoint
        ( inv-equiv f)
        ( inv-equiv g)
        ( inv-commutative-square-inr f g p)
        ( y)
        ( z)
        ( r))
  retraction-cases-retraction-equiv-coproduct f g p x (inr y) z q r =
    ex-falso (equiv-coproduct-induce-equiv-disjoint f g p x y q)

  section-cases-retraction-equiv-coproduct :
    ( f : (A + B) ≃ (A + B)) (g : B ≃ B)
    ( p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    ( x : A) (y z : A + B) (q : map-inv-equiv f (inl x) ＝ y)
    ( r :
      ( map-equiv f (inl (inv-cases-retraction-equiv-coproduct f g p x y q))) ＝
      ( z)) →
    ( cases-retraction-equiv-coproduct f g p
      ( inv-cases-retraction-equiv-coproduct f g p x y q) z r) ＝
    ( x)
  section-cases-retraction-equiv-coproduct f g p x (inl y) (inl z) q r =
    is-injective-inl
      ( ( inv r) ∙
        ( ap (map-equiv f) (inv q)) ∙
        ( ap (λ w → map-equiv w (inl x)) (right-inverse-law-equiv f)))
  section-cases-retraction-equiv-coproduct f g p x (inl y) (inr z) q r =
    ex-falso (equiv-coproduct-induce-equiv-disjoint f g p y z r)
  section-cases-retraction-equiv-coproduct f g p x (inr y) z q r =
    ex-falso
      ( equiv-coproduct-induce-equiv-disjoint
        ( inv-equiv f)
        ( inv-equiv g)
        ( inv-commutative-square-inr f g p)
        ( x)
        ( y)
        ( q))

  retraction-equiv-coproduct :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b)) →
    Σ (A ≃ A) (λ h → htpy-equiv f (equiv-coproduct h g))
  pr1 (pr1 (retraction-equiv-coproduct f g p)) x =
    cases-retraction-equiv-coproduct f g p x (map-equiv f (inl x)) refl
  pr2 (pr1 (retraction-equiv-coproduct f g p)) =
    is-equiv-is-invertible
      ( λ x →
        inv-cases-retraction-equiv-coproduct f g p x
          ( map-inv-equiv f (inl x))
          ( refl))
      ( λ x →
        section-cases-retraction-equiv-coproduct f g p x
          ( map-inv-equiv f (inl x))
          ( map-equiv f
            ( inl
              ( inv-cases-retraction-equiv-coproduct f g p x
                ( map-inv-equiv f (inl x))
                ( refl))))
          ( refl)
          ( refl))
      ( λ x →
        retraction-cases-retraction-equiv-coproduct f g p x
          ( map-equiv f (inl x))
          ( map-inv-equiv f
            ( inl
              ( cases-retraction-equiv-coproduct f g p x
                ( map-equiv f (inl x))
                ( refl))))
          ( refl)
          ( refl))
  pr2 (retraction-equiv-coproduct f g p) (inl x) =
    commutative-square-inl-retraction-equiv-coproduct
      ( x)
      ( map-equiv f (inl x))
      ( refl)
    where
    commutative-square-inl-retraction-equiv-coproduct :
      (x : A) (y : A + B) (q : map-equiv f (inl x) ＝ y) →
      map-equiv f (inl x) ＝ inl (cases-retraction-equiv-coproduct f g p x y q)
    commutative-square-inl-retraction-equiv-coproduct x (inl y) q = q
    commutative-square-inl-retraction-equiv-coproduct x (inr y) q =
      ex-falso (equiv-coproduct-induce-equiv-disjoint f g p x y q)
  pr2 (retraction-equiv-coproduct f g p) (inr x) = p x
```

### Equivalences between mutually exclusive coproducts

If `P → ¬ Q'` and `P' → ¬ Q` then `(P + Q ≃ P' + Q') ≃ ((P ≃ P') × (Q ≃ Q'))`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {P : UU l1} {Q : UU l2} {P' : UU l3} {Q' : UU l4}
  (¬PQ' : P → ¬ Q')
  where

  left-to-left :
    (e : (P + Q) ≃ (P' + Q')) →
    (u : P + Q) → is-left u → is-left (map-equiv e u)
  left-to-left e (inl p) _ =
    ind-coproduct is-left (λ _ → star) (λ q' → ¬PQ' p q') (map-equiv e (inl p))
  left-to-left e (inr q) ()

module _
  {l1 l2 l3 l4 : Level}
  {P : UU l1} {Q : UU l2} {P' : UU l3} {Q' : UU l4}
  (¬P'Q : P' → ¬ Q)
  where

  right-to-right :
    (e : (P + Q) ≃ (P' + Q')) (u : P + Q) →
    is-right u → is-right (map-equiv e u)
  right-to-right e (inl p) ()
  right-to-right e (inr q) _ =
    ind-coproduct is-right (λ p' → ¬P'Q p' q) (λ _ → star) (map-equiv e (inr q))

module _
  {l1 l2 l3 l4 : Level}
  {P : UU l1} {Q : UU l2} {P' : UU l3} {Q' : UU l4}
  (¬PQ' : P → ¬ Q') (¬P'Q : P' → ¬ Q)
  where

  equiv-left-to-left :
    (e : (P + Q) ≃ (P' + Q')) (u : P + Q) → is-left u ≃ is-left (map-equiv e u)
  pr1 (equiv-left-to-left e u) = left-to-left ¬PQ' e u
  pr2 (equiv-left-to-left e u) =
    is-equiv-is-invertible
      ( tr is-left (is-retraction-map-inv-equiv e u) ∘
        left-to-left ¬P'Q (inv-equiv e) (map-equiv e u))
      ( λ _ → eq-is-prop (is-prop-is-left (map-equiv e u)))
      ( λ _ → eq-is-prop (is-prop-is-left u))

  equiv-right-to-right :
    (e : (P + Q) ≃ (P' + Q')) (u : P + Q) →
    is-right u ≃ is-right (map-equiv e u)
  pr1 (equiv-right-to-right e u) = right-to-right ¬P'Q e u
  pr2 (equiv-right-to-right e u) =
    is-equiv-is-invertible
      ( tr is-right (is-retraction-map-inv-equiv e u) ∘
        right-to-right ¬PQ' (inv-equiv e) (map-equiv e u))
      (λ _ → eq-is-prop (is-prop-is-right (map-equiv e u)))
      (λ _ → eq-is-prop (is-prop-is-right u))

  map-mutually-exclusive-coproduct : (P + Q) ≃ (P' + Q') → (P ≃ P') × (Q ≃ Q')
  pr1 (map-mutually-exclusive-coproduct e) =
    equiv-left-summand ∘e
    ( equiv-Σ _ e (equiv-left-to-left e) ∘e
      inv-equiv equiv-left-summand)
  pr2 (map-mutually-exclusive-coproduct e) =
    equiv-right-summand ∘e
    ( equiv-Σ _ e (equiv-right-to-right e) ∘e
      inv-equiv (equiv-right-summand))

  map-inv-mutually-exclusive-coproduct :
    (P ≃ P') × (Q ≃ Q') → (P + Q) ≃ (P' + Q')
  map-inv-mutually-exclusive-coproduct (e₁ , e₂) = equiv-coproduct e₁ e₂

  is-retraction-map-inv-mutually-exclusive-coproduct :
    map-mutually-exclusive-coproduct ∘ map-inv-mutually-exclusive-coproduct ~ id
  is-retraction-map-inv-mutually-exclusive-coproduct (e₁ , e₂) =
    eq-pair
      (eq-equiv-eq-map-equiv refl)
      (eq-equiv-eq-map-equiv refl)

  abstract
    is-section-map-inv-mutually-exclusive-coproduct :
      map-inv-mutually-exclusive-coproduct ∘ map-mutually-exclusive-coproduct ~
      id
    is-section-map-inv-mutually-exclusive-coproduct e =
      eq-htpy-equiv
      ( λ where
        ( inl p) →
          ap
            ( pr1)
            ( is-retraction-map-inv-equiv-left-summand
              ( map-equiv e (inl p) , left-to-left ¬PQ' e (inl p) star))
        ( inr q) →
          ap
            ( pr1)
            ( is-retraction-map-inv-equiv-right-summand
              ( map-equiv e (inr q) , right-to-right ¬P'Q e (inr q) star)))

  equiv-mutually-exclusive-coproduct :
    ((P + Q) ≃ (P' + Q')) ≃ ((P ≃ P') × (Q ≃ Q'))
  pr1 equiv-mutually-exclusive-coproduct = map-mutually-exclusive-coproduct
  pr2 equiv-mutually-exclusive-coproduct =
    is-equiv-is-invertible
      map-inv-mutually-exclusive-coproduct
      is-retraction-map-inv-mutually-exclusive-coproduct
      is-section-map-inv-mutually-exclusive-coproduct
```

### The functorial action of coproducts on arrows

Given a pair of [morphisms of arrows](foundation.morphisms-arrows.md)
`α : f → g` and `β : h → i`, there is an induced morphism of arrows
`α + β : f + h → g + i` and this construction is functorial.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {C : UU l5} {D : UU l6} {Z : UU l7} {W : UU l8}
  (f : A → B) (g : X → Y) (h : C → D) (i : Z → W)
  (α : hom-arrow f g) (β : hom-arrow h i)
  where

  map-domain-coproduct-hom-arrow : A + C → X + Z
  map-domain-coproduct-hom-arrow =
    map-coproduct (map-domain-hom-arrow f g α) (map-domain-hom-arrow h i β)

  map-codomain-coproduct-hom-arrow : B + D → Y + W
  map-codomain-coproduct-hom-arrow =
    map-coproduct (map-codomain-hom-arrow f g α) (map-codomain-hom-arrow h i β)

  coh-coproduct-hom-arrow :
    coherence-hom-arrow
      ( map-coproduct f h)
      ( map-coproduct g i)
      ( map-domain-coproduct-hom-arrow)
      ( map-codomain-coproduct-hom-arrow)
  coh-coproduct-hom-arrow =
    ( inv-htpy
      ( preserves-comp-map-coproduct
        ( f)
        ( map-codomain-hom-arrow f g α)
        ( h)
        ( map-codomain-hom-arrow h i β))) ∙h
    ( htpy-map-coproduct (coh-hom-arrow f g α) (coh-hom-arrow h i β)) ∙h
    ( preserves-comp-map-coproduct
      ( map-domain-hom-arrow f g α) g (map-domain-hom-arrow h i β) i)

  coproduct-hom-arrow : hom-arrow (map-coproduct f h) (map-coproduct g i)
  coproduct-hom-arrow =
    ( map-domain-coproduct-hom-arrow ,
      map-codomain-coproduct-hom-arrow ,
      coh-coproduct-hom-arrow)
```

## See also

- Arithmetical laws involving coproduct types are recorded in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).
- Equality proofs in coproduct types are characterized in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).
- The universal property of coproducts is treated in
  [`foundation.universal-property-coproduct-types`](foundation.universal-property-coproduct-types.md).
- Functorial properties of cartesian product types are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
- Functorial properties of dependent pair types are recorded in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).
