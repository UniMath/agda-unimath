# Free type families

```agda
module foundation.free-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.logical-equivalences
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-identity-types
open import foundation.universe-levels

open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions

open import synthetic-homotopy-theory.joins-of-types
```

</details>

## Definitions

### Free type families

```agda
Fam : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Fam l1 l2 = Σ (UU l1) (λ X → X → UU l2)

module _
  {l1 l2 : Level} (F : Fam l1 l2)
  where

  base-Fam : UU l1
  base-Fam = pr1 F

  family-Fam : base-Fam → UU l2
  family-Fam = pr2 F
```

### Dependent families over a free type family

```agda
Dependent-Fam :
  {l1 l2 : Level} (l3 l4 : Level) → Fam l1 l2 → UU (l1 ⊔ lsuc l3 ⊔ lsuc l4)
Dependent-Fam l3 l4 (A , B) = Σ (A → UU l3) (λ X → (a : A) → X a → UU l4)

Dependent-Fam' :
  {l1 l2 : Level} (l3 l4 : Level) → Fam l1 l2 → UU (l1 ⊔ lsuc l3 ⊔ lsuc l4)
Dependent-Fam' l3 l4 (A , B) = (a : A) → Σ (UU l3) (λ X → X → UU l4)

compute-Dependent-Fam' :
  {l1 l2 l3 l4 : Level} (F : Fam l1 l2) →
  Dependent-Fam' l3 l4 F ≃ Dependent-Fam l3 l4 F
compute-Dependent-Fam' F = distributive-Π-Σ

dependent-fam-Dependent-Fam' :
  {l1 l2 l3 l4 : Level} (F : Fam l1 l2) →
  Dependent-Fam' l3 l4 F → Dependent-Fam l3 l4 F
dependent-fam-Dependent-Fam' F XY = (pr1 ∘ XY , pr2 ∘ XY)

dependent-fam'-Dependent-Fam :
  {l1 l2 l3 l4 : Level} (F : Fam l1 l2) →
  Dependent-Fam l3 l4 F → Dependent-Fam' l3 l4 F
dependent-fam'-Dependent-Fam F (X , Y) a = (X a , Y a)
```

### Doubly dependent families over free type families

```agda
Doubly-Dependent-Fam :
  {l1 l2 l3 l4 : Level} (l5 l6 : Level) →
  (F : Fam l1 l2) → Dependent-Fam l3 l4 F → UU (l1 ⊔ l3 ⊔ lsuc l5 ⊔ lsuc l6)
Doubly-Dependent-Fam l5 l6 (A , B) (X , Y) =
  Σ ((a : A) → X a → UU l5) (λ U → (a : A) (x : X a) → U a x → UU l6)

Doubly-Dependent-Fam' :
  {l1 l2 l3 l4 : Level} (l5 l6 : Level) →
  (F : Fam l1 l2) → Dependent-Fam l3 l4 F → UU (l1 ⊔ l3 ⊔ lsuc l5 ⊔ lsuc l6)
Doubly-Dependent-Fam' l5 l6 (A , B) (X , Y) =
  (a : A) (x : X a) → Σ (UU l5) (λ U → U → UU l6)

compute-Doubly-Dependent-Fam' :
  {l1 l2 l3 l4 l5 l6 : Level} (F : Fam l1 l2) (G : Dependent-Fam l3 l4 F) →
  Doubly-Dependent-Fam' l5 l6 F G ≃ Doubly-Dependent-Fam l5 l6 F G
compute-Doubly-Dependent-Fam' F G =
  distributive-Π-Σ ∘e equiv-Π-equiv-family (λ a → distributive-Π-Σ)

doubly-dependent-fam-Doubly-Dependent-Fam' :
  {l1 l2 l3 l4 l5 l6 : Level} (F : Fam l1 l2) (G : Dependent-Fam l3 l4 F) →
  Doubly-Dependent-Fam' l5 l6 F G → Doubly-Dependent-Fam l5 l6 F G
doubly-dependent-fam-Doubly-Dependent-Fam' F G UV =
  ( (λ a x → pr1 (UV a x)) , (λ a x → pr2 (UV a x)))

doubly-dependent-fam'-Doubly-Dependent-Fam :
  {l1 l2 l3 l4 l5 l6 : Level} (F : Fam l1 l2) (G : Dependent-Fam l3 l4 F) →
  Doubly-Dependent-Fam l5 l6 F G → Doubly-Dependent-Fam' l5 l6 F G
doubly-dependent-fam'-Doubly-Dependent-Fam F G (U , V) a x = (U a x , V a x)
```

### Constant dependent type families

```agda
module _
  {l1 l2 l3 l4 : Level} (F : Fam l1 l2) (G : Fam l3 l4)
  where

  const-Dependent-Fam : Dependent-Fam l3 l4 F
  const-Dependent-Fam = (λ _ → base-Fam G) , (λ _ → family-Fam G)
```

### Dependent morphisms of free type families

```agda
module _
  {l1 l2 l3 l4 : Level}
  (F@(A , B) : Fam l1 l2)
  (G@(X , Y) : Dependent-Fam l3 l4 F)
  where

  dependent-hom-Fam : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  dependent-hom-Fam = Σ ((a : A) → X a) (λ i → (a : A) → B a → Y a (i a))

  dependent-hom-Fam' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  dependent-hom-Fam' = (a : A) → Σ (X a) (λ x → B a → Y a x)
```

### Morphisms of free type families

```agda
module _
  {l1 l2 l3 l4 : Level}
  (F : Fam l1 l2) (G : Fam l3 l4)
  where

  hom-Fam : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Fam = dependent-hom-Fam F (const-Dependent-Fam F G)

  hom-Fam' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Fam' = dependent-hom-Fam' F (const-Dependent-Fam F G)

module _
  {l1 l2 l3 l4 : Level}
  (F : Fam l1 l2) (G : Fam l3 l4) (f : hom-Fam F G)
  where

  map-base-hom-Fam : base-Fam F → base-Fam G
  map-base-hom-Fam = pr1 f

  map-family-hom-Fam :
    (a : base-Fam F) → family-Fam F a → family-Fam G (map-base-hom-Fam a)
  map-family-hom-Fam = pr2 f
```

### The predicate on a morphism of being an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level}
  (F : Fam l1 l2)
  (G : Fam l3 l4)
  (f : hom-Fam F G)
  where

  is-equiv-hom-Fam : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-hom-Fam =
    ( is-equiv (map-base-hom-Fam F G f)) ×
    ( (a : base-Fam F) → is-equiv (map-family-hom-Fam F G f a))

  is-prop-is-equiv-hom-Fam : is-prop is-equiv-hom-Fam
  is-prop-is-equiv-hom-Fam =
    is-prop-product
      ( is-property-is-equiv (map-base-hom-Fam F G f))
      ( is-prop-Π (λ a → is-property-is-equiv (map-family-hom-Fam F G f a)))

  is-equiv-prop-hom-Fam : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-prop-hom-Fam = (is-equiv-hom-Fam , is-prop-is-equiv-hom-Fam)
```

### Equivalences of free type families

```agda
module _
  {l1 l2 l3 l4 : Level}
  (F@(A , B) : Fam l1 l2)
  (G@(X , Y) : Fam l3 l4)
  where

  equiv-Fam : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Fam = Σ (A ≃ X) (λ e → (a : A) → B a ≃ Y (map-equiv e a))
```

### Dependent pullback-exponentials of dependent families over a free type family

```agda
module _
  {l1 l2 l3 l4 : Level}
  (F@(A , B) : Fam l1 l2)
  (G@(X , Y) : Dependent-Fam l3 l4 F)
  where

  base-Π̂-Fam : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  base-Π̂-Fam = dependent-hom-Fam F G

  family-Π̂-Fam : base-Π̂-Fam → UU (l1 ⊔ l2 ⊔ l4)
  family-Π̂-Fam (i , j) =
    Σ ((a : A) → Y a (i a)) (λ y → ((a : A) → j a ~ const (B a) (y a)))

  Π̂-Fam : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  Π̂-Fam = (base-Π̂-Fam , family-Π̂-Fam)

  base-Π̂-Fam' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  base-Π̂-Fam' = dependent-hom-Fam' F G

  family-Π̂-Fam' : base-Π̂-Fam' → UU (l1 ⊔ l2 ⊔ l4)
  family-Π̂-Fam' ij =
    (a : A) → Σ (Y a (pr1 (ij a))) (λ y → (pr2 (ij a) ~ const (B a) y))

  Π̂-Fam' : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  Π̂-Fam' = (base-Π̂-Fam' , family-Π̂-Fam')
```

### Dependent pushout-sums of dependent families over a free type family

```agda
module _
  {l1 l2 l3 l4 : Level}
  (F@(A , B) : Fam l1 l2)
  (G@(X , Y) : Dependent-Fam l3 l4 F)
  where

  base-Σ̂-Fam : UU (l1 ⊔ l3)
  base-Σ̂-Fam = Σ A X

  family-Σ̂-Fam : base-Σ̂-Fam → UU (l2 ⊔ l4)
  family-Σ̂-Fam (a , x) = B a * Y a x

  Σ̂-Fam : Fam (l1 ⊔ l3) (l2 ⊔ l4)
  Σ̂-Fam = (base-Σ̂-Fam , family-Σ̂-Fam)

module _
  {l1 l2 l3 l4 : Level}
  (F : Fam l1 l2)
  (G : Dependent-Fam' l3 l4 F)
  where

  Σ̂-Fam' : Fam (l1 ⊔ l3) (l2 ⊔ l4)
  Σ̂-Fam' = Σ̂-Fam F (dependent-fam-Dependent-Fam' F G)
```

## Theorem

### The dependent Leibniz construction for free type families

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (F@(A , B) : Fam l1 l2)
  (G@(X , Y) : Dependent-Fam l3 l4 F)
  (H@(U , V) : Doubly-Dependent-Fam l5 l6 F G)
  where

  dependent-fam'-Σ̂-Fam : Dependent-Fam' l5 l6 (Σ̂-Fam F G)
  dependent-fam'-Σ̂-Fam (a , x) = (U a x , V a x)

  dependent-fam-Σ̂-Fam : Dependent-Fam l5 l6 (Σ̂-Fam F G)
  dependent-fam-Σ̂-Fam = (rec-Σ U , ind-Σ V)

  dependent-fam'-Π̂-Fam : Dependent-Fam' (l3 ⊔ l4 ⊔ l5 ⊔ l6) (l3 ⊔ l4 ⊔ l6) F
  dependent-fam'-Π̂-Fam a =
    Π̂-Fam
      ( dependent-fam'-Dependent-Fam F G a)
      ( dependent-fam-Dependent-Fam'
        ( dependent-fam'-Dependent-Fam F G a)
        ( doubly-dependent-fam'-Doubly-Dependent-Fam F G H a))

  dependent-fam'-Π̂-Fam' : Dependent-Fam' (l3 ⊔ l4 ⊔ l5 ⊔ l6) (l3 ⊔ l4 ⊔ l6) F
  dependent-fam'-Π̂-Fam' a =
    Π̂-Fam'
      ( dependent-fam'-Dependent-Fam F G a)
      ( dependent-fam-Dependent-Fam'
        ( dependent-fam'-Dependent-Fam F G a)
        ( doubly-dependent-fam'-Doubly-Dependent-Fam F G H a))

  dependent-fam-Π̂-Fam : Dependent-Fam (l3 ⊔ l4 ⊔ l5 ⊔ l6) (l3 ⊔ l4 ⊔ l6) F
  dependent-fam-Π̂-Fam =
    ( λ a →
      Σ ((x : X a) → U a x) (λ i → (x : X a) → Y a x → V a x (i x))) ,
    ( λ a ij@(i , j) →
      Σ ((x : X a) → V a x (i x)) (λ y → (x : X a) → j x ~ const (Y a x) (y x)))

  _ :
    dependent-fam-Π̂-Fam ＝ dependent-fam-Dependent-Fam' F dependent-fam'-Π̂-Fam
  _ = refl

  Π̂-Σ̂-Fam : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6) (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  Π̂-Σ̂-Fam = Π̂-Fam (Σ̂-Fam F G) dependent-fam-Σ̂-Fam

  Π̂-Σ̂-Fam' : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6) (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  Π̂-Σ̂-Fam' =
    ( Σ ( (ax@(a , x) : Σ A X) → U a x)
        ( λ i → (ax@(a , x) : Σ A X) → B a * Y a x → V a x (i ax))) ,
    ( λ ij@(i , j) →
      Σ ( (ax@(a , x) : Σ A X) → V a x (i ax))
        ( λ v → (ax@(a , x) : Σ A X) → j ax ~ const (B a * Y a x) (v ax)))

  _ : Π̂-Σ̂-Fam ＝ Π̂-Σ̂-Fam'
  _ = refl

  Π̂-Σ̂-Fam'' : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6) (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  Π̂-Σ̂-Fam'' = Π̂-Fam' (Σ̂-Fam F G) dependent-fam-Σ̂-Fam

  Π̂-Σ̂-Fam''' : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6) (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  Π̂-Σ̂-Fam''' =
    ( (ax@(a , x) : Σ A X) → Σ (U a x) (λ u → B a * Y a x → V a x u)) ,
    ( λ ij →
      (ax@(a , x) : Σ A X) →
      Σ (V a x (pr1 (ij ax))) (λ v → pr2 (ij ax) ~ const (B a * Y a x) v))

  _ : Π̂-Σ̂-Fam'' ＝ Π̂-Σ̂-Fam'''
  _ = refl

  Π̂²-Fam : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6) (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  Π̂²-Fam = Π̂-Fam F dependent-fam-Π̂-Fam

  Π̂²-Fam' : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6) (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  Π̂²-Fam' =
    ( Σ ( (a : A) →
          Σ ((x : X a) → U a x) (λ i → (x : X a) → Y a x → V a x (i x)))
        ( λ i →
          (a : A) → B a →
          Σ ( (x : X a) → V a x (pr1 (i a) x))
            ( λ v → (x : X a) → pr2 (i a) x ~ const (Y a x) (v x)))) ,
    ( λ ij@(i , j) →
      Σ ( (a : A) →
          Σ ( (x : X a) → V a x (pr1 (i a) x))
            ( λ v → (x : X a) → pr2 (i a) x ~ const (Y a x) (v x)))
        ( λ y → (a : A) → j a ~ const (B a) (y a)))

  _ : Π̂²-Fam ＝ Π̂²-Fam'
  _ = refl

  dependent-fam-Π̂-Fam'' : Dependent-Fam (l3 ⊔ l4 ⊔ l5 ⊔ l6) (l3 ⊔ l4 ⊔ l6) F
  dependent-fam-Π̂-Fam'' =
    ( λ a →
      (x : X a) → Σ (U a x) (λ i → Y a x → V a x i)) ,
    ( λ a ij →
      (x : X a) → Σ (V a x (pr1 (ij x))) (λ v → pr2 (ij x) ~ const (Y a x) v))

  Π̂²-Fam'' : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6) (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  Π̂²-Fam'' = Π̂-Fam' F dependent-fam-Π̂-Fam''

  Π̂²-Fam''' : Fam (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6) (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  Π̂²-Fam''' =
    ( (a : A) →
      Σ ( (x : X a) → Σ (U a x) (λ i → Y a x → V a x i))
        ( λ ij →
          B a → (x : X a) →
          Σ (V a x (pr1 (ij x))) (λ v → pr2 (ij x) ~ const (Y a x) v))) ,
    ( λ ijw →
      (a : A) →
      Σ ( (x : X a) →
          Σ ( V a x (pr1 (pr1 (ijw a) x)))
            ( λ v → pr2 (pr1 (ijw a) x) ~ const (Y a x) v))
        ( λ y → pr2 (ijw a) ~ const (B a) y))

  _ : Π̂²-Fam'' ＝ Π̂²-Fam'''
  _ = refl

  -- dependent-leibniz-construction-Fam :
  --   equiv-Fam Π̂-Σ̂-Fam Π̂²-Fam
  -- dependent-leibniz-construction-Fam =
  --   ( ( equivalence-reasoning
  --       Σ ( (ax@(a , x) : Σ A X) → U a x)
  --         ( λ i → (ax@(a , x) : Σ A X) → B a * Y a x → V a x (i ax))
  --       ≃ Σ ( (a : A) →
  --             Σ ((x : X a) → U a x) (λ i → (x : X a) → Y a x → V a x (i x)))
  --           ( λ ij →
  --             (a : A) → B a →
  --             Σ ( (x : X a) → V a x (pr1 (ij a) x))
  --               ( λ v → (x : X a) → pr2 (ij a) x ~ const (Y a x) (v x)))
  --         by {!   !}) ,
  --     {!   !})
```
