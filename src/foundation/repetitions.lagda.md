# Repetitions of values of maps

```agda
module foundation.repetitions where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.pairs-of-distinct-elements
open import foundation.truncated-maps
open import foundation.universe-levels
```

</details>

## Idea

A repetition of values of a map `f : A → B` consists of a pair of distinct points in `A` that get mapped to the same point in `B`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-repetition-pair-of-distinct-elements :
    (f : A → B) (p : pair-of-distinct-elements A) → UU l2
  is-repetition-pair-of-distinct-elements f p =
    f (fst-pair-of-distinct-elements p) ＝ f (snd-pair-of-distinct-elements p)

  repetition : (A → B) → UU (l1 ⊔ l2)
  repetition f =
    Σ (pair-of-distinct-elements A) (is-repetition-pair-of-distinct-elements f)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (r : repetition f)
  where

  pair-of-distinct-elements-repetition : pair-of-distinct-elements A
  pair-of-distinct-elements-repetition = pr1 r

  fst-repetition : A
  fst-repetition =
    fst-pair-of-distinct-elements pair-of-distinct-elements-repetition

  snd-repetition : A
  snd-repetition =
    snd-pair-of-distinct-elements pair-of-distinct-elements-repetition

  distinction-repetition : ¬ (fst-repetition ＝ snd-repetition)
  distinction-repetition =
    distinction-pair-of-distinct-elements pair-of-distinct-elements-repetition

  is-repetition-pair-of-distinct-elements-repetition :
    is-repetition-pair-of-distinct-elements f
      pair-of-distinct-elements-repetition
  is-repetition-pair-of-distinct-elements-repetition = pr2 r
```

## Properties

### The type of repetitions is invariant under equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (e : A ≃ C) (d : B ≃ D)
  (H : coherence-square-maps (map-equiv e) f g (map-equiv d))
  where

  equiv-repetition : repetition f ≃ repetition g
  equiv-repetition =
    equiv-Σ
      ( λ p →
        ( g (fst-pair-of-distinct-elements p)) ＝
        ( g (snd-pair-of-distinct-elements p)))
      ( equiv-pair-of-distinct-elements e)
      ( λ p →
        ( ( equiv-concat'
            ( g (map-equiv e (fst-pair-of-distinct-elements p)))
            ( H (snd-pair-of-distinct-elements p))) ∘e
          ( equiv-concat
            ( inv (H (fst-pair-of-distinct-elements p)))
            ( map-equiv d (f (snd-pair-of-distinct-elements p))))) ∘e
        ( equiv-ap d
          ( f (fst-pair-of-distinct-elements p))
          ( f (snd-pair-of-distinct-elements p))))

  map-equiv-repetition : repetition f → repetition g
  map-equiv-repetition = map-equiv equiv-repetition

  map-inv-equiv-repetition : repetition g → repetition f
  map-inv-equiv-repetition = map-inv-equiv equiv-repetition

  issec-map-inv-equiv-repetition :
    ( map-equiv-repetition ∘ map-inv-equiv-repetition) ~ id
  issec-map-inv-equiv-repetition = issec-map-inv-equiv equiv-repetition

  isretr-map-inv-equiv-repetition :
    ( map-inv-equiv-repetition ∘ map-equiv-repetition) ~ id
  isretr-map-inv-equiv-repetition = isretr-map-inv-equiv equiv-repetition
```

### Embeddings of repetitions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (e : A ↪ C) (d : B ↪ D)
  (H : coherence-square-maps (map-emb e) f g (map-emb d))
  where

  emb-repetition : repetition f ↪ repetition g
  emb-repetition =
    emb-Σ
      ( λ p →
        ( g (fst-pair-of-distinct-elements p)) ＝
        ( g (snd-pair-of-distinct-elements p)))
      ( emb-pair-of-distinct-elements e)
      ( λ p →
        emb-equiv
          ( ( ( equiv-concat'
                ( g (map-emb e (fst-pair-of-distinct-elements p)))
                ( H (snd-pair-of-distinct-elements p))) ∘e
              ( equiv-concat
                ( inv (H (fst-pair-of-distinct-elements p)))
                ( map-emb d (f (snd-pair-of-distinct-elements p))))) ∘e
            ( equiv-ap-emb d)))

  map-emb-repetition : repetition f → repetition g
  map-emb-repetition = map-emb emb-repetition

  is-emb-map-emb-repetition : is-emb map-emb-repetition
  is-emb-map-emb-repetition = is-emb-map-emb emb-repetition
```
