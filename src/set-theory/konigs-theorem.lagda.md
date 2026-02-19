# Kőnig's theorem

```agda
module set-theory.konigs-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.complements-images
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.law-of-excluded-middle
open import foundation.maps-from-dependent-pair-types-to-dependent-function-types-over-discrete-types
open import foundation.negation
open import foundation.nonsurjective-maps
open import foundation.projective-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.set-truncations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.types-with-decidable-dependent-pair-types
open import foundation.types-with-decidable-existential-quantification
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import logic.propositionally-decidable-maps

open import set-theory.cardinality-projective-sets
open import set-theory.cardinals
open import set-theory.cardinals-with-decidable-existential-quantification
open import set-theory.complemented-inequality-cardinals
open import set-theory.dependent-products-cardinals
open import set-theory.dependent-sums-cardinals
open import set-theory.discrete-cardinals
open import set-theory.inequality-cardinals
open import set-theory.projective-cardinals
open import set-theory.strict-complemented-inequality-cardinals
open import set-theory.strict-indexed-inequality-cardinals
open import set-theory.strict-inequality-cardinals
```

</details>

## Idea

{{#concept "Kőnig's theorem" Disambiguation="for cardinals/set theory" WD="König's theorem" WDID=Q1077462 Agda=le-indexed-Σ-Π-Cardinal}}
states that for any pair of families of [cardinals](set-theory.cardinals.md) $A$
and $B$ over $I$, $Aᵢ < Bᵢ$ for all $i$ then we have that $ΣᵢAᵢ < ΠᵢBᵢ$.

In constructive mathematics we have to be more mindful of our statements than
usual. Here $I$ is any [projective set](foundation.projective-types.md), and by
$Aᵢ < Bᵢ$ we mean that $Bᵢ$ is [inhabited](foundation.inhabited-types.md) and
that for every map $f : Aᵢ → Bᵢ$ there
[exists](foundation.existential-quantification.md) an element of $Bᵢ$ that $f$
does not hit.

## Lemma

Given a projective type $I$ and a pair of families of types $A$ and $B$ over $I$
such that for every $i : I$ every function from $Aᵢ$ to $Bᵢ$ misses an element,
then every function from $ΣᵢAᵢ$ to $ΠᵢBᵢ$ misses an element.

```agda
module _
  {l1 l2 l3 : Level}
  {I : UU l1} (is-projective-I : is-projective-Level (l2 ⊔ l3) I)
  {A : I → UU l2} {B : I → UU l3}
  where

  is-nonsurjective-map-Σ-Π-is-projective-base :
    (H : (i : I) (f : A i → B i) → is-nonsurjective f)
    (g : Σ I A → ((i : I) → B i)) → is-nonsurjective g
  is-nonsurjective-map-Σ-Π-is-projective-base H g =
    map-trunc-Prop
      ( λ h → (pr1 ∘ h , (λ ((i , a) , r) → pr2 (h i) (a , htpy-eq r i))))
      ( is-projective-I
        ( λ i → nonim (λ a → g (i , a) i)) (λ i → H i (λ a → g (i , a) i)))
```

## Theorem

```agda
module _
  {l1 l2 : Level}
  (I : Set l1)
  (is-projective-I : is-projective-Level l2 (type-Set I))
  where

  le-indexed-cardinality-Σ-Π' :
    (A B : type-Set I → Set l2) →
    ((i : type-Set I) → le-indexed-cardinality' (A i) (B i)) →
    le-indexed-cardinality' (Σ-Set I A) (Π-Set I B)
  le-indexed-cardinality-Σ-Π' A B p =
    ( is-projective-I (type-Set ∘ B) (pr1 ∘ p) ,
      is-nonsurjective-map-Σ-Π-is-projective-base is-projective-I (pr2 ∘ p))

  le-indexed-cardinality-Σ-Π :
    (A B : type-Set I → Set l2) →
    ((i : type-Set I) → le-indexed-cardinality (A i) (B i)) →
    le-indexed-cardinality (Σ-Set I A) (Π-Set I B)
  le-indexed-cardinality-Σ-Π A B p =
    unit-le-indexed-cardinality
      ( Σ-Set I A)
      ( Π-Set I B)
      ( le-indexed-cardinality-Σ-Π' A B
        ( λ i → inv-unit-le-indexed-cardinality (A i) (B i) (p i)))

module _
  {l1 l2 : Level}
  (I : Projective-Set l1 (lsuc l2))
  (let set-I = set-Projective-Set I)
  (let type-I = type-Projective-Set I)
  (let I' = cardinality-projective-set-Projective-Set I)
  where

  le-indexed-Σ-Π-Cardinal :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → le-indexed-Cardinal (A i) (B i)) →
    le-indexed-Cardinal (Σ-Cardinal I' A) (Π-Cardinal I' B)
  le-indexed-Σ-Π-Cardinal =
    apply-twice-ind-Cardinality-Projective-Set I'
      ( λ A B →
        set-Prop
          ( function-Prop
            ( (i : type-I) → le-indexed-Cardinal (A i) (B i))
            ( le-indexed-prop-Cardinal
              ( Σ-Cardinal I' A)
              ( Π-Cardinal I' B))))
      ( λ A B p →
        binary-tr
          ( le-indexed-Cardinal)
          ( inv (compute-Σ-Cardinal I' A))
          ( inv (compute-Π-Cardinal I' B))
          ( le-indexed-cardinality-Σ-Π
            ( set-I)
            ( is-projective-is-projective-lsuc-Level l2
              ( is-projective-Projective-Set I))
            ( A)
            ( B)
            ( p)))
```

## Corollaries

We derive versions of Kőnig's theorem for other notions of strict inequality of
cardinals, under additional assumptions on the indexing set and cardinals.

### Kőnig's theorem for strict inequality

```agda
module _
  {l1 l2 : Level}
  (I : Cardinality-Projective-Set l1 l2)
  (let type-I = type-Cardinality-Projective-Set I)
  where

  le-indexed-Σ-Π-le-family-Cardinal :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (A i)) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (B i)) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (B i)) →
    ((i : type-I) → le-Cardinal (A i) (B i)) →
    le-indexed-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-indexed-Σ-Π-le-family-Cardinal
    A B merely-Σ-A is-projective-B is-discrete-B merely-Σ-B H =
    le-indexed-Σ-Π-Cardinal I A B
      ( λ i →
        le-indexed-le-Cardinal
          ( A i)
          ( B i)
          ( merely-Σ-A i)
          ( is-projective-B i)
          ( is-discrete-B i)
          ( merely-Σ-B i)
          ( H i))
```

### Kőnig's theorem for strict complemented inequality

```agda
module _
  {l1 l2 : Level}
  (I : Cardinality-Projective-Set l1 l2)
  (let type-I = type-Cardinality-Projective-Set I)
  where

  le-indexed-Σ-Π-le-complemented-family-Cardinal :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → is-discrete-Cardinal (A i)) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (A i)) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (B i)) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (B i)) →
    ((i : type-I) → le-complemented-Cardinal (A i) (B i)) →
    le-indexed-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-indexed-Σ-Π-le-complemented-family-Cardinal
    A B is-discrete-A merely-Σ-A is-projective-B is-discrete-B merely-Σ-B H =
    le-indexed-Σ-Π-Cardinal I A B
      ( λ i →
        le-indexed-le-complemented-Cardinal
          ( A i)
          ( B i)
          ( is-discrete-A i)
          ( merely-Σ-A i)
          ( is-projective-B i)
          ( is-discrete-B i)
          ( merely-Σ-B i)
          ( H i))
```

### Kőnig's theorem for strict inequality

```agda
module _
  {l1 l2 : Level}
  (I : Cardinality-Projective-Set l1 l2)
  (dI : has-decidable-equality (type-Cardinality-Projective-Set I))
  (let type-I = type-Cardinality-Projective-Set I)
  (let set-I = set-Cardinality-Projective-Set I)
  where

  leq-cardinality-Σ-Π-le-family :
    (A B : type-I → Set l2) →
    ((i : type-I) → merely-decidable-∃-cardinality l2 (A i)) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → is-discrete-cardinality (B i)) →
    ((i : type-I) → merely-decidable-∃-cardinality l2 (B i)) →
    ((i : type-I) → le-cardinality (A i) (B i)) →
    leq-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  leq-cardinality-Σ-Π-le-family
    A B merely-Σ-A is-projective-B is-discrete-B merely-Σ-B H =
    let
      nonsurjective-emb :
        (e : (i : type-I) → type-Set (A i) ↪ type-Set (B i)) →
        (i : type-I) → is-nonsurjective (pr1 (e i))
      nonsurjective-emb e i =
        pr2
          ( inv-unit-le-indexed-cardinality
            ( A i)
            ( B i)
            ( le-indexed-le-cardinality
              ( A i)
              ( B i)
              ( inv-unit-merely-decidable-∃-cardinality (A i) (merely-Σ-A i))
              ( is-projective-B i)
              ( inv-unit-is-discrete-cardinality (B i) (is-discrete-B i))
              ( inv-unit-merely-decidable-∃-cardinality (B i) (merely-Σ-B i))
              ( H i)))
          ( pr1 (e i))

      build-emb :
        ((i : type-I) → type-Set (A i) ↪ type-Set (B i)) →
        type-trunc-Prop (type-Set (Σ-Set set-I A) ↪ type-Set (Π-Set set-I B))
      build-emb e =
        map-trunc-Prop
          ( emb-Σ-Π-nonim-Set (type-I , dI) A B e)
          ( is-projective-Cardinality-Projective-Set I
            ( λ i → nonim (pr1 (e i)))
            ( λ i → nonsurjective-emb e i))
    in
    unit-leq-cardinality
      ( Σ-Set set-I A)
      ( Π-Set set-I B)
      ( map-idempotent-trunc-Prop
        ( type-Set (Σ-Set set-I A) ↪ type-Set (Π-Set set-I B))
        ( map-trunc-Prop
          ( build-emb)
          ( is-projective-Cardinality-Projective-Set I
            ( λ i → type-Set (A i) ↪ type-Set (B i))
            ( λ i → inv-unit-leq-cardinality (A i) (B i) (pr1 (H i))))))

module _
  {l1 l2 : Level}
  (wlpo : level-WLPO (l1 ⊔ l2))
  (I : Cardinality-Projective-Set l1 l2)
  (dI : has-decidable-equality (type-Cardinality-Projective-Set I))
  (let type-I = type-Cardinality-Projective-Set I)
  (let set-I = set-Cardinality-Projective-Set I)
  where

  le-cardinality-Σ-Π :
    (A B : type-I → Set l2) →
    is-discrete-cardinality (Σ-Set set-I A) →
    ((i : type-I) → merely-decidable-∃-cardinality l2 (A i)) →
    merely-decidable-∃-cardinality (l1 ⊔ l2) (Σ-Set set-I A) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → is-discrete-cardinality (B i)) →
    is-discrete-cardinality (Π-Set set-I B) →
    ((i : type-I) → merely-decidable-∃-cardinality l2 (B i)) →
    merely-decidable-∃-cardinality (l1 ⊔ l2) (Π-Set set-I B) →
    ((i : type-I) → le-cardinality (A i) (B i)) →
    le-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  le-cardinality-Σ-Π A B is-discrete-Σ merely-Σ-A merely-Σ-Σ
    is-projective-B is-discrete-B is-discrete-Π merely-Σ-B merely-Σ-Π H =
    le-le-indexed-leq-cardinality-WLPO
      ( wlpo)
      ( Σ-Set set-I A)
      ( Π-Set set-I B)
      ( inv-unit-is-discrete-cardinality (Σ-Set set-I A) is-discrete-Σ)
      ( inv-unit-merely-decidable-∃-cardinality
        ( Σ-Set set-I A)
        ( merely-Σ-Σ))
      ( inv-unit-is-discrete-cardinality (Π-Set set-I B) is-discrete-Π)
      ( inv-unit-merely-decidable-∃-cardinality
        ( Π-Set set-I B)
        ( merely-Σ-Π))
      ( leq-cardinality-Σ-Π-le-family I dI A B merely-Σ-A
        ( is-projective-B)
        ( is-discrete-B)
        ( merely-Σ-B)
        ( H))
      ( le-indexed-cardinality-Σ-Π
        ( set-I)
        ( is-projective-Cardinality-Projective-Set I)
        ( A)
        ( B)
        ( λ i →
          le-indexed-le-cardinality
            ( A i)
            ( B i)
            ( inv-unit-merely-decidable-∃-cardinality (A i) (merely-Σ-A i))
            ( is-projective-B i)
            ( inv-unit-is-discrete-cardinality (B i) (is-discrete-B i))
            ( inv-unit-merely-decidable-∃-cardinality (B i) (merely-Σ-B i))
            ( H i)))

  le-Σ-Π-Cardinal :
    (A B : type-I → Cardinal l2) →
    is-discrete-Cardinal (Σ-Cardinal I A) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (A i)) →
    merely-decidable-∃-Cardinal (l1 ⊔ l2) (Σ-Cardinal I A) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (B i)) →
    is-discrete-Cardinal (Π-Cardinal I B) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (B i)) →
    merely-decidable-∃-Cardinal (l1 ⊔ l2) (Π-Cardinal I B) →
    ((i : type-I) → le-Cardinal (A i) (B i)) →
    le-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-Σ-Π-Cardinal =
    apply-twice-ind-Cardinality-Projective-Set I
      ( λ A B →
        set-Prop
          ( function-Prop
            ( is-discrete-Cardinal (Σ-Cardinal I A))
            ( function-Prop
              ( (i : type-I) → merely-decidable-∃-Cardinal l2 (A i))
              ( function-Prop
                ( merely-decidable-∃-Cardinal (l1 ⊔ l2) (Σ-Cardinal I A))
                ( function-Prop
                  ( (i : type-I) → is-projective-Cardinal l2 (B i))
                  ( function-Prop
                    ( (i : type-I) → is-discrete-Cardinal (B i))
                    ( function-Prop
                      ( is-discrete-Cardinal (Π-Cardinal I B))
                      ( function-Prop
                        ( (i : type-I) → merely-decidable-∃-Cardinal l2 (B i))
                        ( function-Prop
                          ( merely-decidable-∃-Cardinal
                            ( l1 ⊔ l2)
                            ( Π-Cardinal I B))
                          ( function-Prop
                            ( (i : type-I) → le-Cardinal (A i) (B i))
                            ( le-prop-Cardinal
                              ( Σ-Cardinal I A)
                              ( Π-Cardinal I B))))))))))))
      ( λ A B is-discrete-Σ merely-Σ-A merely-Σ-Σ is-projective-B is-discrete-B
      is-discrete-Π merely-Σ-B merely-Σ-Π H →
        binary-tr
          ( le-Cardinal)
          ( inv (compute-Σ-Cardinal I A))
          ( inv (compute-Π-Cardinal I B))
          ( le-cardinality-Σ-Π A B
            ( tr is-discrete-Cardinal
              ( compute-Σ-Cardinal I A)
              ( is-discrete-Σ))
            ( merely-Σ-A)
            ( tr (merely-decidable-∃-Cardinal (l1 ⊔ l2))
              ( compute-Σ-Cardinal I A)
              ( merely-Σ-Σ))
            ( λ i →
              inv-unit-is-projective-cardinality (B i) (is-projective-B i))
            ( is-discrete-B)
            ( tr is-discrete-Cardinal
              ( compute-Π-Cardinal I B)
              ( is-discrete-Π))
            ( merely-Σ-B)
            ( tr (merely-decidable-∃-Cardinal (l1 ⊔ l2))
              ( compute-Π-Cardinal I B)
              ( merely-Σ-Π))
            ( H)))
```

### Kőnig's theorem for strict inequality, assuming LEM

```agda
module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (I : Cardinality-Projective-Set l1 l2)
  (dI : has-decidable-equality (type-Cardinality-Projective-Set I))
  (let type-I = type-Cardinality-Projective-Set I)
  (let set-I = set-Cardinality-Projective-Set I)
  where

  private
    lem-l2 : level-LEM (l2 ⊔ l2)
    lem-l2 P =
      is-decidable-equiv
        ( compute-raise l1 (type-Prop P))
        ( lem (raise-Prop l1 P))

  leq-cardinality-Σ-Π-le-family-LEM :
    (A B : type-I → Set l2) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → le-cardinality (A i) (B i)) →
    leq-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  leq-cardinality-Σ-Π-le-family-LEM A B is-projective-B H =
    let
      nonsurjective-emb :
        (e : (i : type-I) → type-Set (A i) ↪ type-Set (B i)) →
        (i : type-I) → is-nonsurjective (pr1 (e i))
      nonsurjective-emb e i =
        pr2
          ( inv-unit-le-indexed-cardinality
            ( A i)
            ( B i)
            ( le-indexed-le-cardinality-LEM
              ( lem-l2)
              ( A i)
              ( B i)
              ( is-projective-B i)
              ( H i)))
          ( pr1 (e i))

      build-emb :
        ((i : type-I) → type-Set (A i) ↪ type-Set (B i)) →
        type-trunc-Prop
          ( type-Set (Σ-Set set-I A) ↪ type-Set (Π-Set set-I B))
      build-emb e =
        map-trunc-Prop
          ( emb-Σ-Π-nonim-Set (type-I , dI) A B e)
          ( is-projective-Cardinality-Projective-Set I
            ( λ i → nonim (pr1 (e i)))
            ( λ i → nonsurjective-emb e i))
    in
    unit-leq-cardinality
      ( Σ-Set set-I A)
      ( Π-Set set-I B)
      ( map-idempotent-trunc-Prop
        ( type-Set (Σ-Set set-I A) ↪ type-Set (Π-Set set-I B))
        ( map-trunc-Prop
          ( build-emb)
          ( is-projective-Cardinality-Projective-Set I
            ( λ i → type-Set (A i) ↪ type-Set (B i))
            ( λ i → inv-unit-leq-cardinality (A i) (B i) (pr1 (H i))))))

  le-cardinality-Σ-Π-LEM :
    (A B : type-I → Set l2) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → le-cardinality (A i) (B i)) →
    le-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  le-cardinality-Σ-Π-LEM A B is-projective-B H =
    le-le-indexed-leq-cardinality
      ( lem)
      ( Σ-Set set-I A)
      ( Π-Set set-I B)
      ( leq-cardinality-Σ-Π-le-family-LEM A B is-projective-B H)
      ( le-indexed-cardinality-Σ-Π
        ( set-I)
        ( is-projective-Cardinality-Projective-Set I)
        ( A)
        ( B)
        ( λ i →
          le-indexed-le-cardinality-LEM
            ( lem-l2)
            ( A i)
            ( B i)
            ( is-projective-B i)
            ( H i)))

  le-Σ-Π-Cardinal-LEM :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → le-Cardinal (A i) (B i)) →
    le-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-Σ-Π-Cardinal-LEM =
    apply-twice-ind-Cardinality-Projective-Set I
      ( λ A B →
        set-Prop
          ( function-Prop
            ( (i : type-I) → is-projective-Cardinal l2 (B i))
            ( function-Prop
              ( (i : type-I) → le-Cardinal (A i) (B i))
              ( le-prop-Cardinal
                ( Σ-Cardinal I A)
                ( Π-Cardinal I B)))))
      ( λ A B is-projective-B H →
        binary-tr
          ( le-Cardinal)
          ( inv (compute-Σ-Cardinal I A))
          ( inv (compute-Π-Cardinal I B))
          ( le-cardinality-Σ-Π-LEM A B
            ( λ i →
              inv-unit-is-projective-cardinality (B i) (is-projective-B i))
            ( H)))
```

### Kőnig's theorem for strict complemented inequality

```agda
module _
  {l1 l2 : Level}
  (I : Cardinality-Projective-Set l1 l2)
  (dI : has-decidable-equality (type-Cardinality-Projective-Set I))
  (decidable-Σ-I : has-decidable-Σ (type-Cardinality-Projective-Set I))
  (let type-I = type-Cardinality-Projective-Set I)
  (let set-I = set-Cardinality-Projective-Set I)
  where

  leq-complemented-cardinality-Σ-Π :
    (A B : type-I → Set l2) →
    ((i : type-I) → is-discrete-cardinality (A i)) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → is-discrete-cardinality (B i)) →
    ((i : type-I) → merely-decidable-∃-cardinality l2 (B i)) →
    ((i : type-I) → le-complemented-cardinality (A i) (B i)) →
    leq-complemented-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  leq-complemented-cardinality-Σ-Π
    A B is-discrete-A is-projective-B is-discrete-B merely-Σ-B H =
    let
      dec-emb-Σ-Π :
        (e : (i : type-I) → type-Set (A i) ↪ᵈ type-Set (B i)) →
        ((i : type-I) → nonim (map-decidable-emb (e i))) →
        type-Set (Σ-Set set-I A) ↪ᵈ type-Set (Π-Set set-I B)
      dec-emb-Σ-Π e b =
        let
          emb-Σ-Π =
            emb-Σ-Π-nonim-Set (type-I , dI) A B (emb-decidable-emb ∘ e) b
          dec-Σ-Π =
            is-decidable-map-Σ-Π-nonim
              ( type-I , dI)
              ( decidable-Σ-I)
              ( λ i → inv-unit-is-discrete-cardinality (B i) (is-discrete-B i))
              ( map-decidable-emb ∘ e)
              ( b)
              ( is-decidable-map-map-decidable-emb ∘ e)
        in
        ( pr1 emb-Σ-Π , (pr2 emb-Σ-Π , dec-Σ-Π))

      nonsurjective-emb :
        (e : (i : type-I) → type-Set (A i) ↪ᵈ type-Set (B i)) →
        (i : type-I) → is-nonsurjective (map-decidable-emb (e i))
      nonsurjective-emb e i =
        rec-trunc-Prop
          ( is-nonsurjective-Prop (map-decidable-emb (e i)))
          ( λ hΣB →
            is-nonsurjective-is-not-surjective-has-decidable-∃-is-inhabited-or-empty-map
              ( hΣB)
              ( is-inhabited-or-empty-map-is-decidable-map
                ( is-decidable-map-map-decidable-emb (e i)))
              ( ( pr2 (H i)) ∘
                ( geq-complemented-is-surjective-cardinality
                  ( A i)
                  ( B i)
                  ( inv-unit-is-discrete-cardinality (A i) (is-discrete-A i))
                  ( is-projective-B i)
                  ( map-decidable-emb (e i)))))
          ( inv-unit-merely-decidable-∃-cardinality (B i) (merely-Σ-B i))

      build-emb :
        ((i : type-I) → type-Set (A i) ↪ᵈ type-Set (B i)) →
        type-trunc-Prop (type-Set (Σ-Set set-I A) ↪ᵈ type-Set (Π-Set set-I B))
      build-emb e =
        map-trunc-Prop
          ( dec-emb-Σ-Π e)
          ( is-projective-Cardinality-Projective-Set I
            ( λ i → nonim (map-decidable-emb (e i)))
            ( nonsurjective-emb e))
    in
    unit-leq-complemented-cardinality
      ( Σ-Set set-I A)
      ( Π-Set set-I B)
      ( map-idempotent-trunc-Prop
        ( type-Set (Σ-Set set-I A) ↪ᵈ type-Set (Π-Set set-I B))
        ( map-trunc-Prop
          ( build-emb)
          ( is-projective-Cardinality-Projective-Set I
            ( λ i → type-Set (A i) ↪ᵈ type-Set (B i))
            ( λ i →
              inv-unit-leq-complemented-cardinality (A i) (B i) (pr1 (H i))))))

module _
  {l1 l2 : Level}
  (wlpo : level-WLPO (l1 ⊔ l2))
  (I : Cardinality-Projective-Set l1 l2)
  (dI : has-decidable-equality (type-Cardinality-Projective-Set I))
  (decidable-Σ-I : has-decidable-Σ (type-Cardinality-Projective-Set I))
  (let type-I = type-Cardinality-Projective-Set I)
  (let set-I = set-Cardinality-Projective-Set I)
  where

  le-complemented-cardinality-Σ-Π :
    (A B : type-I → Set l2) →
    ((i : type-I) → is-discrete-cardinality (A i)) →
    ((i : type-I) → merely-decidable-∃-cardinality l2 (A i)) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → is-discrete-cardinality (B i)) →
    ((i : type-I) → merely-decidable-∃-cardinality l2 (B i)) →
    ((i : type-I) → le-complemented-cardinality (A i) (B i)) →
    le-complemented-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  le-complemented-cardinality-Σ-Π
    A B is-discrete-A merely-Σ-A is-projective-B is-discrete-B merely-Σ-B H =
    le-complemented-le-indexed-leq-complemented-cardinality
      ( wlpo)
      ( Σ-Set set-I A)
      ( Π-Set set-I B)
      ( leq-complemented-cardinality-Σ-Π
          I dI decidable-Σ-I A B is-discrete-A
          is-projective-B is-discrete-B merely-Σ-B H)
      ( le-indexed-cardinality-Σ-Π
        ( set-I)
        ( is-projective-Cardinality-Projective-Set I)
        ( A)
        ( B)
        ( λ i →
          le-indexed-le-complemented-cardinality
            ( A i)
            ( B i)
            ( inv-unit-is-discrete-cardinality (A i) (is-discrete-A i))
            ( inv-unit-merely-decidable-∃-cardinality (A i) (merely-Σ-A i))
            ( is-projective-B i)
            ( inv-unit-is-discrete-cardinality (B i) (is-discrete-B i))
            ( inv-unit-merely-decidable-∃-cardinality (B i) (merely-Σ-B i))
            ( H i)))

  le-complemented-Σ-Π-Cardinal :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → is-discrete-Cardinal (A i)) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (A i)) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (B i)) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (B i)) →
    ((i : type-I) → le-complemented-Cardinal (A i) (B i)) →
    le-complemented-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-complemented-Σ-Π-Cardinal =
    apply-twice-ind-Cardinality-Projective-Set I
      ( λ A B →
        set-Prop
          ( function-Prop
            ( (i : type-I) → is-discrete-Cardinal (A i))
            ( function-Prop
              ( (i : type-I) → merely-decidable-∃-Cardinal l2 (A i))
              ( function-Prop
                ( (i : type-I) → is-projective-Cardinal l2 (B i))
                ( function-Prop
                  ( (i : type-I) → is-discrete-Cardinal (B i))
                  ( function-Prop
                    ( (i : type-I) → merely-decidable-∃-Cardinal l2 (B i))
                    ( function-Prop
                      ( (i : type-I) → le-complemented-Cardinal (A i) (B i))
                      ( le-complemented-prop-Cardinal
                        ( Σ-Cardinal I A)
                        ( Π-Cardinal I B)))))))))
      ( λ A B is-discrete-A merely-Σ-A
      is-projective-B is-discrete-B merely-Σ-B H →
        binary-tr
          ( le-complemented-Cardinal)
          ( inv (compute-Σ-Cardinal I A))
          ( inv (compute-Π-Cardinal I B))
          ( le-complemented-cardinality-Σ-Π A B is-discrete-A merely-Σ-A
            ( λ i →
              inv-unit-is-projective-cardinality (B i) (is-projective-B i))
            ( is-discrete-B)
            ( merely-Σ-B)
            ( H)))
```

### Kőnig's theorem for strict inequality, assuming WLPO

```agda
module _
  {l1 l2 : Level}
  (wlpo : WLPO)
  (I : Cardinality-Projective-Set l1 l2)
  (dI : has-decidable-equality (type-Cardinality-Projective-Set I))
  (let type-I = type-Cardinality-Projective-Set I)
  where

  le-Σ-Π-Cardinal-WLPO :
    (A B : type-I → Cardinal l2) →
    is-discrete-Cardinal (Σ-Cardinal I A) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (A i)) →
    merely-decidable-∃-Cardinal (l1 ⊔ l2) (Σ-Cardinal I A) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (B i)) →
    is-discrete-Cardinal (Π-Cardinal I B) →
    ((i : type-I) → merely-decidable-∃-Cardinal l2 (B i)) →
    merely-decidable-∃-Cardinal (l1 ⊔ l2) (Π-Cardinal I B) →
    ((i : type-I) → le-Cardinal (A i) (B i)) →
    le-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-Σ-Π-Cardinal-WLPO =
    apply-twice-ind-Cardinality-Projective-Set I
      ( λ A B →
        set-Prop
          ( function-Prop
            ( is-discrete-Cardinal (Σ-Cardinal I A))
            ( function-Prop
              ( (i : type-I) → merely-decidable-∃-Cardinal l2 (A i))
              ( function-Prop
                ( merely-decidable-∃-Cardinal (l1 ⊔ l2) (Σ-Cardinal I A))
                ( function-Prop
                  ( (i : type-I) → is-projective-Cardinal l2 (B i))
                  ( function-Prop
                    ( (i : type-I) → is-discrete-Cardinal (B i))
                    ( function-Prop
                      ( is-discrete-Cardinal (Π-Cardinal I B))
                      ( function-Prop
                        ( (i : type-I) → merely-decidable-∃-Cardinal l2 (B i))
                        ( function-Prop
                          ( merely-decidable-∃-Cardinal
                            ( l1 ⊔ l2)
                            ( Π-Cardinal I B))
                          ( function-Prop
                            ( (i : type-I) → le-Cardinal (A i) (B i))
                            ( le-prop-Cardinal
                              ( Σ-Cardinal I A)
                              ( Π-Cardinal I B))))))))))))
      ( λ A B is-discrete-Σ merely-Σ-A merely-Σ-Σ is-projective-B is-discrete-B
      is-discrete-Π merely-Σ-B merely-Σ-Π H →
        binary-tr
          ( le-Cardinal)
          ( inv (compute-Σ-Cardinal I A))
          ( inv (compute-Π-Cardinal I B))
          ( le-cardinality-Σ-Π
            ( wlpo)
            ( I)
            ( dI)
            ( A)
            ( B)
            ( tr is-discrete-Cardinal
              ( compute-Σ-Cardinal I A)
              ( is-discrete-Σ))
            ( merely-Σ-A)
            ( tr (merely-decidable-∃-Cardinal (l1 ⊔ l2))
              ( compute-Σ-Cardinal I A)
              ( merely-Σ-Σ))
            ( λ i →
              inv-unit-is-projective-cardinality (B i) (is-projective-B i))
            ( is-discrete-B)
            ( tr is-discrete-Cardinal
              ( compute-Π-Cardinal I B)
              ( is-discrete-Π))
            ( merely-Σ-B)
            ( tr (merely-decidable-∃-Cardinal (l1 ⊔ l2))
              ( compute-Π-Cardinal I B)
              ( merely-Σ-Π))
            ( H)))
```

## External links

- [Kőnig's theorem (set theory)](<https://en.wikipedia.org/wiki/K%C5%91nig%27s_theorem_(set_theory)>)
  on Wikipedia
