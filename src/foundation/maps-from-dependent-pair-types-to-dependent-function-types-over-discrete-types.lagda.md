# Maps from dependent sums and dependent products over discrete types

```agda
module foundation.maps-from-dependent-pair-types-to-dependent-function-types-over-discrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.evaluation-functions
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.nonsurjective-maps
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.types-with-decidable-dependent-pair-types
open import foundation.universe-levels
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
        ( is-injective-injection ∘ f))
```

### If `f` has retractions then `A i` is a retract of `(i : I') → B i` for every `i`

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
    (r : (i : I') → retraction (f i)) →
    (i : I') → ((i : I') → B i) → A i
  map-retraction-map-at-Π-nonim r i =
    map-retraction (f i) (r i) ∘ ev-point i

  is-retraction-map-retraction-map-at-Π-nonim :
    (r : (i : I') → retraction (f i)) (i : I') →
    is-retraction (map-at-Π-nonim i) (map-retraction-map-at-Π-nonim r i)
  is-retraction-map-retraction-map-at-Π-nonim r i a =
    ( ap
      ( map-retraction (f i) (r i))
      ( compute-diagonal-map-Σ-Π-nonim I f b i a)) ∙
    ( is-retraction-map-retraction (f i) (r i) a)

  retraction-map-at-Π-nonim :
    (r : (i : I') → retraction (f i)) →
    (i : I') → retraction (map-at-Π-nonim i)
  retraction-map-at-Π-nonim r i =
    ( map-retraction-map-at-Π-nonim r i ,
      is-retraction-map-retraction-map-at-Π-nonim r i)

  retract-at-Π-nonim :
    (r : (i : I') → retraction (f i)) →
    (i : I') → A i retract-of ((i : I') → B i)
  retract-at-Π-nonim r i =
    ( map-at-Π-nonim i , retraction-map-at-Π-nonim r i)
```

### If `Bᵢ` is a set and `fᵢ` is an injection then the induced map from `Σ I A` to `Π I B` is an embedding

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  where

  emb-Σ-Π-nonim-Set' :
    {A : I' → UU l2} (B : I' → Set l3) →
    (f : (i : I') → injection (A i) (type-Set (B i))) →
    (b : (i : I') → nonim (map-injection (f i))) →
    Σ I' A ↪ ((i : I') → type-Set (B i))
  emb-Σ-Π-nonim-Set' B f b =
    emb-injection (Π-Set (set-Discrete-Type I) B) (injection-Σ-Π-nonim I f b)

  emb-Σ-Π-nonim-Set :
    (A : I' → Set l2) (B : I' → Set l3) →
    (f : (i : I') → type-Set (A i) ↪ type-Set (B i)) →
    (b : (i : I') → nonim (pr1 (f i))) →
    Σ I' (type-Set ∘ A) ↪ ((i : I') → type-Set (B i))
  emb-Σ-Π-nonim-Set A B f = emb-Σ-Π-nonim-Set' B (injection-emb ∘ f)
```

### Decidability of the induced map from `Σ I A` to `Π I B`

When `I` has decidable sums, each `Bᵢ` is discrete, and `f` is a decidable map,
then the induced map from `Σ I A` to `Π I B` is also decidable.

```agda
module _
  {l1 l2 l3 : Level}
  (I : Discrete-Type l1)
  (let I' = type-Discrete-Type I)
  {A : I' → UU l2} {B : I' → UU l3}
  where

  is-decidable-map-Σ-Π-nonim :
    has-decidable-Σ I' →
    ((i : I') → has-decidable-equality (B i)) →
    (f : (i : I') → A i → B i)
    (b : (i : I') → nonim (f i)) →
    ((i : I') → is-decidable-map (f i)) →
    is-decidable-map (map-Σ-Π-nonim I f b)
  is-decidable-map-Σ-Π-nonim hI dB f b dF g =
    map-coproduct
      ( λ (i , p) → fromP i p)
      ( λ noP t → noP (toP t))
      ( hI (P , decP))
    where
      b' : (i : I') → B i
      b' = pr1 ∘ b

      Q : I' → UU (l1 ⊔ l3)
      Q i = (j : I') → j ≠ i → g j ＝ b' j

      is-decidable-Q : (i : I') → is-decidable (Q i)
      is-decidable-Q i =
        rec-coproduct
          ( λ (j , (neq , neqb)) → inr (λ q → neqb (q j neq)))
          ( λ no-counter →
              inl
                ( λ j neq →
                  rec-coproduct
                    ( λ p → p)
                    ( λ np →
                      ex-falso (no-counter (j , (neq , np))))
                    ( dB j (g j) (b' j))))
          ( hI
            ( (λ j → (j ≠ i) × (g j ≠ b' j)) ,
              ( λ j →
                is-decidable-product
                  ( is-decidable-neg
                    ( has-decidable-equality-type-Discrete-Type I j i))
                  ( is-decidable-neg (dB j (g j) (b' j))))))

      P : I' → UU (l1 ⊔ l2 ⊔ l3)
      P i = fiber (f i) (g i) × Q i

      decP : (i : I') → is-decidable (P i)
      decP i = is-decidable-product (dF i (g i)) (is-decidable-Q i)

      toP : fiber (map-Σ-Π-nonim I f b) g → Σ I' P
      toP ((i , a) , p) =
        ( i ,
          ( ( a ,
              ( inv
                ( compute-diagonal-map-Σ-Π-nonim I f b i a) ∙
                ( ap (ev i) p))) ,
            ( λ j neq →
              ( inv (ap (ev j) p)) ∙
              ( compute-distinct-map-Σ-Π-nonim I f b (λ q → neq (inv q)) a))))

      fromP : (i : I') → P i → fiber (map-Σ-Π-nonim I f b) g
      fromP i ((a , p) , q) =
        ( (i , a) ,
          eq-htpy
            ( λ j →
              ind-coproduct
                ( λ s →
                  rec-coproduct (λ r → tr B r (f i a)) (λ _ → b' j) s ＝ g j)
                ( λ r → ap (tr B r) p ∙ apd g r)
                ( λ neq → inv (q j (λ r → neq (inv r))))
                ( has-decidable-equality-type-Discrete-Type I i j)))
```

## See also

- This map is used in the construction of
  [Kőnig's theorem](set-theory.konigs-theorem.md)
