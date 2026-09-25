# Maps from dependent sums to dependent products over a discrete type

```agda
module foundation.maps-from-dependent-pair-types-to-dependent-function-types-over-discrete-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.complements-images
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.discrete-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.evaluation-functions
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.mere-decidable-embeddings
open import foundation.mere-embeddings
open import foundation.negated-equality
open import foundation.negation
open import foundation.nonsurjective-maps
open import foundation.projective-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.types-with-decidable-existential-quantifications
open import foundation.universe-levels

open import logic.propositionally-decidable-types
```

</details>

## Idea

Given a family of maps `fᵢ : A i → B i` over a
[discrete type](foundation-core.discrete-types.md) `I` such that for each `i`
there is an element `bᵢ : B i` that is
[not in the image](foundation.nonsurjective-maps.md) of `fᵢ`, then we construct
a map `f' : Σ A → Π B` such that `f' (i , a) i = fᵢ a` and `f' (i , a) j = bⱼ`
if `i ≠ j`. If `f` is an [injection](foundation-core.injective-maps.md) then so
is this map.

## Construction

### The induced map from `Σ I A` to `Π I B`

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  {A : I' → UU l2} {B : I' → UU l3}
  (f : (i : I') → A i → B i)
  (b : (i : I') → nonim (f i))
  (let b' = pr1 ∘ b)
  where

  map-Σ-Π-nonim : Σ I' A → (i : I') → B i
  map-Σ-Π-nonim (i , a) j =
    rec-coproduct
      ( λ p → tr B p (f i a))
      ( λ _ → b' j)
      ( has-decidable-equality-type-Discrete-Type I i j)

  compute-diagonal-map-Σ-Π-nonim :
    (i : I') (a : A i) → map-Σ-Π-nonim (i , a) i ＝ f i a
  compute-diagonal-map-Σ-Π-nonim i a =
    ind-coproduct
      ( λ s → rec-coproduct (λ p → tr B p (f i a)) (λ _ → b' i) s ＝ f i a)
      ( λ p →
        ap
          ( λ q → tr B q (f i a))
          ( eq-is-prop' (is-set-type-Discrete-Type I i i) p refl))
      ( λ n → ex-falso (n refl))
      ( has-decidable-equality-type-Discrete-Type I i i)

  compute-distinct-map-Σ-Π-nonim :
    {i j : I'} → i ≠ j → (a : A i) →
    map-Σ-Π-nonim (i , a) j ＝ b' j
  compute-distinct-map-Σ-Π-nonim {i} {j} i≠j a =
    ind-coproduct
      ( λ s → rec-coproduct (λ p → tr B p (f i a)) (λ _ → b' j) s ＝ b' j)
      ( λ p → ex-falso (i≠j p))
      ( λ _ → refl)
      ( has-decidable-equality-type-Discrete-Type I i j)
```

### If `f` is a family of injections then so is the induced map from `Σ I A` to `Π I B`

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  {A : I' → UU l2} {B : I' → UU l3}
  where

  is-injective-map-Σ-Π-nonim :
    (f : (i : I') → A i → B i)
    (b : (i : I') → nonim (f i)) →
    ((i : I') → is-injective (f i)) →
    is-injective (map-Σ-Π-nonim I f b)
  is-injective-map-Σ-Π-nonim
    f b is-injective-f {x = (i , a)} {y = (i' , a')} p =
    rec-coproduct
      ( λ q →
        ( eq-pair-eq-fiber
          ( is-injective-f i
            ( ( inv (compute-diagonal-map-Σ-Π-nonim I f b i a)) ∙
              ( ap (ev i) (p ∙ ap (map-Σ-Π-nonim I f b) (eq-pair-eq-base q))) ∙
              ( compute-diagonal-map-Σ-Π-nonim I f b i (tr A q a'))))) ∙
        ( inv (eq-pair-eq-base q)))
      ( λ neq →
        ex-falso
          ( pr2
            ( b i)
            ( a ,
              ( inv (compute-diagonal-map-Σ-Π-nonim I f b i a)) ∙
              ( ap (ev i) p) ∙
              ( compute-distinct-map-Σ-Π-nonim I f b neq a'))))
      ( has-decidable-equality-type-Discrete-Type I i' i)

  injection-Σ-Π-nonim :
    (f : (i : I') → injection (A i) (B i)) →
    (b : (i : I') → nonim (map-injection (f i))) →
    injection (Σ I' A) ((i : I') → B i)
  injection-Σ-Π-nonim f b =
    ( map-Σ-Π-nonim I (map-injection ∘ f) b ,
      is-injective-map-Σ-Π-nonim
        ( map-injection ∘ f)
        ( b)
        ( is-injective-map-injection ∘ f))
```

### If `fᵢ` has a retraction then `Aᵢ` is a retract of `(i : I) → Bᵢ`

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  {A : I' → UU l2} {B : I' → UU l3}
  (f : (i : I') → A i → B i)
  (b : (i : I') → nonim (f i))
  where

  map-at-Π-nonim : (i : I') → A i → (i : I') → B i
  map-at-Π-nonim i a = map-Σ-Π-nonim I f b (i , a)

  map-retraction-map-at-Π-nonim :
    (i : I') (r : retraction (f i)) → ((i : I') → B i) → A i
  map-retraction-map-at-Π-nonim i r =
    map-retraction (f i) r ∘ ev-point i

  is-retraction-map-retraction-map-at-Π-nonim :
    (i : I') (r : retraction (f i)) →
    is-retraction (map-at-Π-nonim i) (map-retraction-map-at-Π-nonim i r)
  is-retraction-map-retraction-map-at-Π-nonim i r a =
    ( ap
      ( map-retraction (f i) r)
      ( compute-diagonal-map-Σ-Π-nonim I f b i a)) ∙
    ( is-retraction-map-retraction (f i) r a)

  retraction-map-at-Π-nonim :
    (i : I') (r : retraction (f i)) → retraction (map-at-Π-nonim i)
  retraction-map-at-Π-nonim i r =
    ( map-retraction-map-at-Π-nonim i r ,
      is-retraction-map-retraction-map-at-Π-nonim i r)

  retract-at-Π-nonim :
    (i : I') (r : retraction (f i)) → A i retract-of ((i : I') → B i)
  retract-at-Π-nonim i r =
    ( map-at-Π-nonim i , retraction-map-at-Π-nonim i r)
```

### If `Bᵢ` is a set and `fᵢ` is an injection then the induced map from `Σ I A` to `Π I B` is an embedding

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  where

  emb-Σ-Π-nonim-Set :
    {A : I' → UU l2} (B : I' → Set l3) →
    (f : (i : I') → injection (A i) (type-Set (B i))) →
    (b : (i : I') → nonim (map-injection (f i))) →
    Σ I' A ↪ ((i : I') → type-Set (B i))
  emb-Σ-Π-nonim-Set B f b =
    emb-injection (Π-Set (set-Discrete-Type I) B) (injection-Σ-Π-nonim I f b)
```

### A description of the fibers of the induced map

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  {A : I' → UU l2} {B : I' → UU l3}
  (f : (i : I') → A i → B i)
  (b : (i : I') → nonim (f i))
  (g : (i : I') → B i)
  (let b' = pr1 ∘ b)
  where

  off-diagonal-Σ-Π-nonim : I' → UU (l1 ⊔ l3)
  off-diagonal-Σ-Π-nonim i = (j : I') → j ≠ i → g j ＝ b' j

  fiber-at-Σ-Π-nonim : I' → UU (l1 ⊔ l2 ⊔ l3)
  fiber-at-Σ-Π-nonim i = fiber (f i) (g i) × off-diagonal-Σ-Π-nonim i

  fiber-description-Σ-Π-nonim :
    (i : I') → fiber-at-Σ-Π-nonim i → fiber (map-Σ-Π-nonim I f b) g
  fiber-description-Σ-Π-nonim i ((a , p) , q) =
    ( (i , a) ,
      eq-htpy
        ( λ j →
          ind-coproduct
            ( λ s → rec-coproduct (λ r → tr B r (f i a)) (λ _ → b' j) s ＝ g j)
            ( λ r → ap (tr B r) p ∙ apd g r)
            ( λ neq → inv (q j (λ r → neq (inv r))))
            ( has-decidable-equality-type-Discrete-Type I i j)))
```

### Decidability of the off-diagonal condition

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  {A : I' → UU l2} {B : I' → UU l3}
  (f : (i : I') → A i → B i)
  (b : (i : I') → nonim (f i))
  (g : (i : I') → B i)
  (let b' = pr1 ∘ b)
  where

  is-decidable-off-diagonal-Σ-Π-nonim :
    has-decidable-∃-bool I' →
    ((i : I') → has-decidable-equality (B i)) →
    (i : I') → is-decidable (off-diagonal-Σ-Π-nonim I f b g i)
  is-decidable-off-diagonal-Σ-Π-nonim hI dB i =
    rec-coproduct
      ( inr ∘ rec-trunc-Prop
        ( neg-type-Prop (off-diagonal-Σ-Π-nonim I f b g i))
        ( λ (j , (neq , neqb)) q → neqb (q j neq)))
      ( λ nc →
        inl
          ( λ j neq →
            rec-coproduct
              ( λ p → p)
              ( λ np → ex-falso (nc (unit-trunc-Prop (j , (neq , np)))))
              ( dB j (g j) (b' j))))
      ( has-decidable-∃-has-decidable-∃-bool hI
        ( (λ j → (j ≠ i) × (g j ≠ b' j)) ,
          ( λ j →
            is-decidable-product
              ( is-decidable-neg
                ( has-decidable-equality-type-Discrete-Type I j i))
              ( is-decidable-neg (dB j (g j) (b' j))))))
```

### The active coordinate of a fiber is unique

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  {A : I' → UU l2} {B : I' → UU l3}
  (f : (i : I') → A i → B i)
  (b : (i : I') → nonim (f i))
  (g : (i : I') → B i)
  (dB : (i : I') → has-decidable-equality (B i))
  where

  candidate-fiber-at-Σ-Π-nonim-Prop : I' → Prop (l1 ⊔ l2 ⊔ l3)
  candidate-fiber-at-Σ-Π-nonim-Prop i =
    product-Prop
      ( trunc-Prop (fiber (f i) (g i)))
      ( Π-Prop I'
        ( λ j →
          function-Prop
            ( j ≠ i)
            ( g j ＝ pr1 (b j) ,
              is-set-has-decidable-equality (dB j) (g j) (pr1 (b j)))))

  candidate-fiber-Σ-Π-nonim : UU (l1 ⊔ l2 ⊔ l3)
  candidate-fiber-Σ-Π-nonim =
    type-subtype candidate-fiber-at-Σ-Π-nonim-Prop

  is-prop-candidate-fiber-Σ-Π-nonim : is-prop candidate-fiber-Σ-Π-nonim
  is-prop-candidate-fiber-Σ-Π-nonim =
    is-prop-all-elements-equal
      ( λ (i , (p , q)) (j , (p' , q')) →
        eq-type-subtype candidate-fiber-at-Σ-Π-nonim-Prop
          ( rec-coproduct
            ( id)
            ( λ neq →
              ex-falso
                ( rec-trunc-Prop empty-Prop
                  ( λ (a , r) → pr2 (b i) (a , r ∙ q' i neq))
                  ( p)))
            ( has-decidable-equality-type-Discrete-Type I i j)))

  candidate-fiber-Σ-Π-nonim-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  candidate-fiber-Σ-Π-nonim-Prop =
    ( candidate-fiber-Σ-Π-nonim , is-prop-candidate-fiber-Σ-Π-nonim)

  candidate-of-fiber-Σ-Π-nonim :
    fiber (map-Σ-Π-nonim I f b) g → candidate-fiber-Σ-Π-nonim
  candidate-of-fiber-Σ-Π-nonim ((i , a) , p) =
    ( i ,
      unit-trunc-Prop
        ( a , inv (compute-diagonal-map-Σ-Π-nonim I f b i a) ∙ ap (ev i) p) ,
      ( λ j neq →
        inv (ap (ev j) p) ∙
        compute-distinct-map-Σ-Π-nonim I f b (λ q → neq (inv q)) a))

  fiber-candidate-Σ-Π-nonim :
    ((i : I') → is-decidable-map (f i)) →
    candidate-fiber-Σ-Π-nonim → fiber (map-Σ-Π-nonim I f b) g
  fiber-candidate-Σ-Π-nonim dF (i , (p , q)) =
    rec-coproduct
      ( λ t → fiber-description-Σ-Π-nonim I f b g i (t , q))
      ( λ nf → ex-falso (rec-trunc-Prop empty-Prop nf p))
      ( dF i (g i))
```

### Decidability of the induced map

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  {A : I' → UU l2} {B : I' → UU l3}
  where

  is-decidable-map-Σ-Π-nonim :
    has-decidable-∃-bool I' →
    ((i : I') → has-decidable-equality (B i)) →
    (f : (i : I') → A i → B i)
    (b : (i : I') → nonim (f i)) →
    ((i : I') → is-decidable-map (f i)) →
    is-decidable-map (map-Σ-Π-nonim I f b)
  is-decidable-map-Σ-Π-nonim hI dB f b dF g =
    map-coproduct
      ( fiber-candidate-Σ-Π-nonim I f b g dB dF ∘
        rec-trunc-Prop (candidate-fiber-Σ-Π-nonim-Prop I f b g dB) id)
      ( λ nc → nc ∘ unit-trunc-Prop ∘ candidate-of-fiber-Σ-Π-nonim I f b g dB)
      ( has-decidable-∃-has-decidable-∃-bool hI
        ( ( λ i → type-Prop (candidate-fiber-at-Σ-Π-nonim-Prop I f b g dB i)) ,
          ( λ i →
            is-decidable-product
              ( is-decidable-trunc-Prop-is-decidable (dF i (g i)))
              ( is-decidable-off-diagonal-Σ-Π-nonim I f b g hI dB i))))
```

### Families of nonsurjective mere embeddings over projective types

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  (is-projective-I : is-projective-Level (l2 ⊔ l3) I')
  (A : I' → UU l2) (B : I' → Set l3)
  where

  mere-emb-Σ-Π-is-projective :
    ((i : I') → mere-emb (A i) (type-Set (B i))) →
    ((i : I') (e : A i ↪ type-Set (B i)) → is-nonsurjective (map-emb e)) →
    mere-emb (Σ I' A) ((i : I') → type-Set (B i))
  mere-emb-Σ-Π-is-projective E H =
    map-trunc-Prop
      ( λ h → emb-Σ-Π-nonim-Set I B (λ i → injection-emb (pr1 (h i))) (pr2 ∘ h))
      ( is-projective-I
        ( λ i → Σ (A i ↪ type-Set (B i)) (λ e → nonim (map-emb e)))
        ( λ i →
          rec-trunc-Prop
            ( trunc-Prop (Σ (A i ↪ type-Set (B i)) (λ e → nonim (map-emb e))))
            ( λ e → map-trunc-Prop (pair e) (H i e))
            ( E i)))
```

### The induced decidable embedding

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  (decidable-∃-I : has-decidable-∃-bool I')
  {A : I' → UU l2} {B : I' → UU l3}
  (dB : (i : I') → has-decidable-equality (B i))
  where

  decidable-emb-Σ-Π-nonim :
    (e : (i : I') → A i ↪ᵈ B i) →
    ((i : I') → nonim (map-decidable-emb (e i))) →
    Σ I' A ↪ᵈ ((i : I') → B i)
  decidable-emb-Σ-Π-nonim e b =
    ( map-Σ-Π-nonim I (map-decidable-emb ∘ e) b ,
      ( is-emb-map-emb
          ( emb-Σ-Π-nonim-Set I
            ( λ i → (B i , is-set-has-decidable-equality (dB i)))
            ( injection-emb ∘ emb-decidable-emb ∘ e)
            ( b)) ,
        is-decidable-map-Σ-Π-nonim I decidable-∃-I dB
          ( map-decidable-emb ∘ e) b
          ( is-decidable-map-map-decidable-emb ∘ e)))
```

### Families of nonsurjective mere decidable embeddings over projective types

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  (is-projective-I : is-projective-Level (l2 ⊔ l3) I')
  (decidable-∃-I : has-decidable-∃-bool I')
  (A : I' → UU l2) (B : I' → UU l3)
  (dB : (i : I') → has-decidable-equality (B i))
  where

  mere-decidable-emb-Σ-Π-is-projective :
    ((i : I') → mere-decidable-emb (A i) (B i)) →
    ( (i : I') (e : A i ↪ᵈ B i) →
      is-nonsurjective (map-decidable-emb e)) →
    mere-decidable-emb (Σ I' A) ((i : I') → B i)
  mere-decidable-emb-Σ-Π-is-projective E H =
    map-trunc-Prop
      ( λ h → decidable-emb-Σ-Π-nonim I decidable-∃-I dB (pr1 ∘ h) (pr2 ∘ h))
      ( is-projective-I
        ( λ i → Σ (A i ↪ᵈ B i) (λ e → nonim (map-decidable-emb e)))
        ( λ i →
          rec-trunc-Prop
            ( trunc-Prop (Σ (A i ↪ᵈ B i) (λ e → nonim (map-decidable-emb e))))
            ( λ e → map-trunc-Prop (pair e) (H i e))
            ( E i)))
```

## See also

- This map is used in the construction of
  [Kőnig's theorem](set-theory.konigs-theorem.md)
