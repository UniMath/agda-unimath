# Repetitions of values of maps

```agda
module foundation.repetitions-of-values where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.pairs-of-distinct-elements
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A
{{#concept "repetition of values" Disambiguation="of a map of types" Agda=repetition-of-values}}
of a map `f : A → B` consists of a
[pair of distinct elements](foundation.pairs-of-distinct-elements.md) `x ≠ y` of
`A` that get mapped to the [same](foundation-core.identity-types.md) element in
`B`: `f x ＝ f y`.

## Definitions

### The predicate that a pair of distinct elements is a repetition of values

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-repetition-of-values : (A → B) → pair-of-distinct-elements A → UU l2
  is-repetition-of-values f p =
    f (first-pair-of-distinct-elements p) ＝
    f (second-pair-of-distinct-elements p)

  repetition-of-values : (A → B) → UU (l1 ⊔ l2)
  repetition-of-values f =
    Σ ( pair-of-distinct-elements A)
      ( is-repetition-of-values f)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (r : repetition-of-values f)
  where

  pair-of-distinct-elements-repetition-of-values : pair-of-distinct-elements A
  pair-of-distinct-elements-repetition-of-values = pr1 r

  first-repetition-of-values : A
  first-repetition-of-values =
    first-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values

  second-repetition-of-values : A
  second-repetition-of-values =
    second-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values

  distinction-repetition-of-values :
    first-repetition-of-values ≠ second-repetition-of-values
  distinction-repetition-of-values =
    distinction-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values

  is-repetition-of-values-repetition-of-values :
    is-repetition-of-values f pair-of-distinct-elements-repetition-of-values
  is-repetition-of-values-repetition-of-values = pr2 r
```

### The predicate that an element is repeated

```agda
is-repeated-value :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → A → UU (l1 ⊔ l2)
is-repeated-value {A = A} f a =
  Σ (Σ A (λ x → a ≠ x)) (λ x → f a ＝ f (pr1 x))
```

## Properties

### Maps with repetitions of values are not injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-not-injective-repetition-of-values :
    repetition-of-values f → ¬ (is-injective f)
  is-not-injective-repetition-of-values r H =
    distinction-repetition-of-values f r
      ( H (is-repetition-of-values-repetition-of-values f r))
```

### Repetitions of values of composite maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  repetition-of-values-comp :
    repetition-of-values f → repetition-of-values (g ∘ f)
  repetition-of-values-comp ((x , y , s) , t) =
    ((x , y , s) , ap g t)

  repetition-of-values-left-factor' :
    is-injective f → repetition-of-values (g ∘ f) → repetition-of-values g
  repetition-of-values-left-factor' H ((a , b , K) , p) =
    ((f a , f b , λ q → K (H q)) , p)

  repetition-of-values-left-factor :
    is-emb f → repetition-of-values (g ∘ f) → repetition-of-values g
  repetition-of-values-left-factor H =
    repetition-of-values-left-factor' (is-injective-is-emb H)

  repetition-of-values-right-factor' :
    is-injective g → repetition-of-values (g ∘ f) → repetition-of-values f
  repetition-of-values-right-factor' H ((a , b , K) , p) = ((a , b , K) , H p)

  repetition-of-values-right-factor :
    is-emb g → repetition-of-values (g ∘ f) → repetition-of-values f
  repetition-of-values-right-factor H =
    repetition-of-values-right-factor' (is-injective-is-emb H)
```

### The type of repetitions of values is invariant under equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (e : A ≃ C) (d : B ≃ D)
  (H : coherence-square-maps (map-equiv e) f g (map-equiv d))
  where

  equiv-repetition-of-values : repetition-of-values f ≃ repetition-of-values g
  equiv-repetition-of-values =
    equiv-Σ
      ( λ p →
        ( g (first-pair-of-distinct-elements p)) ＝
        ( g (second-pair-of-distinct-elements p)))
      ( equiv-pair-of-distinct-elements e)
      ( λ p →
        ( ( equiv-concat'
            ( g (map-equiv e (first-pair-of-distinct-elements p)))
            ( H (second-pair-of-distinct-elements p))) ∘e
          ( equiv-concat
            ( inv (H (first-pair-of-distinct-elements p)))
            ( map-equiv d (f (second-pair-of-distinct-elements p))))) ∘e
        ( equiv-ap d
          ( f (first-pair-of-distinct-elements p))
          ( f (second-pair-of-distinct-elements p))))

  map-equiv-repetition-of-values :
    repetition-of-values f → repetition-of-values g
  map-equiv-repetition-of-values =
    map-equiv equiv-repetition-of-values

  map-inv-equiv-repetition-of-values :
    repetition-of-values g → repetition-of-values f
  map-inv-equiv-repetition-of-values = map-inv-equiv equiv-repetition-of-values

  is-section-map-inv-equiv-repetition-of-values :
    is-section
      ( map-equiv-repetition-of-values)
      ( map-inv-equiv-repetition-of-values)
  is-section-map-inv-equiv-repetition-of-values =
    is-section-map-inv-equiv equiv-repetition-of-values

  is-retraction-map-inv-equiv-repetition-of-values :
    is-retraction
      ( map-equiv-repetition-of-values)
      ( map-inv-equiv-repetition-of-values)
  is-retraction-map-inv-equiv-repetition-of-values =
    is-retraction-map-inv-equiv equiv-repetition-of-values
```

### Embeddings of repetitions of values

Given an embedding of arrows `f ↪ g`, i.e. a commuting square

```text
         e
    A ------> C
    |         |
  f |         | g
    ∨         ∨
    B ------> D
         d
```

where `e` and `d` are embeddings, then the type of repetitions of values of `f`
embeds into the type of repetitions of values of `g`.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (e : A ↪ C) (d : B ↪ D)
  (H : coherence-square-maps (map-emb e) f g (map-emb d))
  where

  emb-repetition-of-values : repetition-of-values f ↪ repetition-of-values g
  emb-repetition-of-values =
    emb-Σ
      ( λ p →
        ( g (first-pair-of-distinct-elements p)) ＝
        ( g (second-pair-of-distinct-elements p)))
      ( emb-pair-of-distinct-elements e)
      ( λ p →
        emb-equiv
          ( ( ( equiv-concat'
                ( g (map-emb e (first-pair-of-distinct-elements p)))
                ( H (second-pair-of-distinct-elements p))) ∘e
              ( equiv-concat
                ( inv (H (first-pair-of-distinct-elements p)))
                ( map-emb d (f (second-pair-of-distinct-elements p))))) ∘e
            ( equiv-ap-emb d)))

  map-emb-repetition-of-values : repetition-of-values f → repetition-of-values g
  map-emb-repetition-of-values = map-emb emb-repetition-of-values

  is-emb-map-emb-repetition-of-values : is-emb map-emb-repetition-of-values
  is-emb-map-emb-repetition-of-values = is-emb-map-emb emb-repetition-of-values
```

## See also

- [Noninjective maps](foundation.noninjective-maps.md)
