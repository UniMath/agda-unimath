# Kőnig's theorem

```agda
module set-theory.konigs-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
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
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import logic.propositionally-decidable-maps

open import set-theory.cardinality-projective-sets
open import set-theory.cardinals
open import set-theory.cardinals-with-merely-decidable-sums
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
usual. Here $I$ is any
[cardinality-projective set](set-theory.cardinality-projective-sets.md) and by
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
  {I : UU l1} (p : is-projective-Level' (l2 ⊔ l3) I)
  {A : I → UU l2} {B : I → UU l3}
  where

  is-nonsurjective-map-Σ-Π-is-projective-base' :
    (H : (i : I) (f : A i → B i) → is-nonsurjective f)
    (g : Σ I A → ((i : I) → B i)) → is-nonsurjective g
  is-nonsurjective-map-Σ-Π-is-projective-base' H g =
    map-trunc-Prop
      ( λ h → (pr1 ∘ h , (λ ((i , a) , r) → pr2 (h i) (a , htpy-eq r i))))
      ( p (λ i → nonim (λ a → g (i , a) i)) (λ i → H i (λ a → g (i , a) i)))
```

## Theorem

```agda
module _
  {l1 l2 : Level}
  (I : Set l1)
  (is-projective-I : is-projective-Level' l2 (type-Set I))
  where

  le-indexed-cardinality-Σ-Π' :
    (A B : type-Set I → Set l2) →
    ((i : type-Set I) → le-indexed-cardinality' (A i) (B i)) →
    le-indexed-cardinality' (Σ-Set I A) (Π-Set I B)
  le-indexed-cardinality-Σ-Π' A B p =
    ( is-projective-I (type-Set ∘ B) (pr1 ∘ p) ,
      is-nonsurjective-map-Σ-Π-is-projective-base' is-projective-I (pr2 ∘ p))

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
  (I : Cardinality-Projective-Set l1 l2)
  (let type-I = type-Cardinality-Projective-Set I)
  (let set-I = set-Cardinality-Projective-Set I)
  where

  le-indexed-Σ-Π-Cardinal :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → le-indexed-Cardinal (A i) (B i)) →
    le-indexed-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-indexed-Σ-Π-Cardinal =
    apply-twice-ind-Cardinality-Projective-Set I
      ( λ A B →
        set-Prop
          ( function-Prop
            ( (i : type-I) → le-indexed-Cardinal (A i) (B i))
            ( le-indexed-prop-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B))))
      ( λ A B p →
        binary-tr
          ( le-indexed-Cardinal)
          ( inv (compute-Σ-Cardinal I A))
          ( inv (compute-Π-Cardinal I B))
          ( le-indexed-cardinality-Σ-Π
            ( set-I)
            ( is-projective-Cardinality-Projective-Set I)
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
    ((i : type-I) → le-Cardinal (A i) (B i)) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (B i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (B i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (A i)) →
    le-indexed-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-indexed-Σ-Π-le-family-Cardinal A B H is-projective-B is-discrete-B
    merely-Σ-B merely-Σ-A =
    le-indexed-Σ-Π-Cardinal I A B
      ( λ i →
        le-indexed-le-Cardinal
          ( A i)
          ( B i)
          ( is-projective-B i)
          ( is-discrete-B i)
          ( merely-Σ-B i)
          ( merely-Σ-A i)
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
    ((i : type-I) → le-complemented-Cardinal (A i) (B i)) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (B i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (A i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (A i)) →
    le-indexed-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-indexed-Σ-Π-le-complemented-family-Cardinal
    A B H is-projective-B is-discrete-B merely-Σ-B is-discrete-A merely-Σ-A =
    le-indexed-Σ-Π-Cardinal I A B
      ( λ i →
        le-indexed-le-complemented-Cardinal
          ( A i)
          ( B i)
          ( is-projective-B i)
          ( is-discrete-B i)
          ( merely-Σ-B i)
          ( is-discrete-A i)
          ( merely-Σ-A i)
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
    ((i : type-I) → le-cardinality (A i) (B i)) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → is-discrete-cardinality (B i)) →
    ((i : type-I) → merely-decidable-Σ-cardinality l2 (B i)) →
    ((i : type-I) → merely-decidable-Σ-cardinality l2 (A i)) →
    leq-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  leq-cardinality-Σ-Π-le-family A B H is-projective-B is-discrete-B
    merely-Σ-B merely-Σ-A =
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
              ( is-projective-B i)
              ( inv-unit-is-discrete-cardinality (B i) (is-discrete-B i))
              ( inv-unit-merely-decidable-Σ-cardinality (B i) (merely-Σ-B i))
              ( inv-unit-merely-decidable-Σ-cardinality (A i) (merely-Σ-A i))
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

module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (I : Cardinality-Projective-Set l1 l2)
  (dI : has-decidable-equality (type-Cardinality-Projective-Set I))
  (let type-I = type-Cardinality-Projective-Set I)
  (let set-I = set-Cardinality-Projective-Set I)
  where

  le-cardinality-Σ-Π :
    (A B : type-I → Set l2) →
    ((i : type-I) → le-cardinality (A i) (B i)) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → is-discrete-cardinality (B i)) →
    ((i : type-I) → merely-decidable-Σ-cardinality l2 (B i)) →
    ((i : type-I) → merely-decidable-Σ-cardinality l2 (A i)) →
    le-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  le-cardinality-Σ-Π A B H is-projective-B is-discrete-B merely-Σ-B merely-Σ-A =
    le-le-indexed-leq-cardinality
      ( lem)
      ( Σ-Set set-I A)
      ( Π-Set set-I B)
      ( leq-cardinality-Σ-Π-le-family I dI A B H is-projective-B is-discrete-B
        merely-Σ-B merely-Σ-A)
      ( le-indexed-cardinality-Σ-Π
        ( set-I)
        ( is-projective-Cardinality-Projective-Set I)
        ( A)
        ( B)
        ( λ i →
          le-indexed-le-cardinality
            ( A i)
            ( B i)
            ( is-projective-B i)
            ( inv-unit-is-discrete-cardinality (B i) (is-discrete-B i))
            ( inv-unit-merely-decidable-Σ-cardinality (B i) (merely-Σ-B i))
            ( inv-unit-merely-decidable-Σ-cardinality (A i) (merely-Σ-A i))
            ( H i)))

  le-Σ-Π-Cardinal :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → le-Cardinal (A i) (B i)) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (B i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (B i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (A i)) →
    le-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-Σ-Π-Cardinal =
    apply-twice-ind-Cardinality-Projective-Set I
      ( λ A B →
        set-Prop
          ( function-Prop
            ( (i : type-I) → le-Cardinal (A i) (B i))
            ( function-Prop
              ( (i : type-I) → is-projective-Cardinal l2 (B i))
              ( function-Prop
                ( (i : type-I) → is-discrete-Cardinal (B i))
                ( function-Prop
                  ( (i : type-I) → merely-decidable-Σ-Cardinal l2 (B i))
                  ( function-Prop
                    ( (i : type-I) → merely-decidable-Σ-Cardinal l2 (A i))
                    ( le-prop-Cardinal
                      (Σ-Cardinal I A) (Π-Cardinal I B))))))))
      ( λ A B H is-projective-B is-discrete-B merely-Σ-B merely-Σ-A →
        binary-tr
          ( le-Cardinal)
          ( inv (compute-Σ-Cardinal I A))
          ( inv (compute-Π-Cardinal I B))
          ( le-cardinality-Σ-Π A B H
            ( λ i →
              inv-unit-is-projective-cardinality (B i) (is-projective-B i))
            ( λ i → is-discrete-B i)
            ( merely-Σ-B)
            ( merely-Σ-A)))
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
    ((i : type-I) → le-complemented-cardinality (A i) (B i)) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → is-discrete-cardinality (B i)) →
    ((i : type-I) → merely-decidable-Σ-cardinality l2 (B i)) →
    ((i : type-I) → is-discrete-cardinality (A i)) →
    leq-complemented-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  leq-complemented-cardinality-Σ-Π
    A B H is-projective-B is-discrete-B merely-Σ-B is-discrete-A =
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
            is-nonsurjective-is-not-surjective-has-decidable-Σ-Level-is-inhabited-or-empty-map
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
          ( inv-unit-merely-decidable-Σ-cardinality (B i) (merely-Σ-B i))

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
    ((i : type-I) → le-complemented-cardinality (A i) (B i)) →
    ((i : type-I) → is-projective-Level' l2 (type-Set (B i))) →
    ((i : type-I) → is-discrete-cardinality (B i)) →
    ((i : type-I) → merely-decidable-Σ-cardinality l2 (B i)) →
    ((i : type-I) → is-discrete-cardinality (A i)) →
    ((i : type-I) → merely-decidable-Σ-cardinality l2 (A i)) →
    le-complemented-cardinality (Σ-Set set-I A) (Π-Set set-I B)
  le-complemented-cardinality-Σ-Π
    A B H is-projective-B is-discrete-B merely-Σ-B is-discrete-A merely-Σ-A =
    le-complemented-le-indexed-leq-complemented-cardinality
      ( wlpo)
      ( Σ-Set set-I A)
      ( Π-Set set-I B)
      ( leq-complemented-cardinality-Σ-Π
          I dI decidable-Σ-I A B H
          is-projective-B is-discrete-B merely-Σ-B is-discrete-A)
      ( le-indexed-cardinality-Σ-Π
        ( set-I)
        ( is-projective-Cardinality-Projective-Set I)
        ( A)
        ( B)
        ( λ i →
          le-indexed-le-complemented-cardinality
            ( A i)
            ( B i)
            ( is-projective-B i)
            ( inv-unit-is-discrete-cardinality (B i) (is-discrete-B i))
            ( inv-unit-merely-decidable-Σ-cardinality (B i) (merely-Σ-B i))
            ( inv-unit-is-discrete-cardinality (A i) (is-discrete-A i))
            ( inv-unit-merely-decidable-Σ-cardinality (A i) (merely-Σ-A i))
            ( H i)))

  le-complemented-Σ-Π-Cardinal :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → le-complemented-Cardinal (A i) (B i)) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (B i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (B i)) →
    ((i : type-I) → is-discrete-Cardinal (A i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (A i)) →
    le-complemented-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-complemented-Σ-Π-Cardinal =
    apply-twice-ind-Cardinality-Projective-Set I
      ( λ A B →
        set-Prop
          ( function-Prop
            ( (i : type-I) → le-complemented-Cardinal (A i) (B i))
            ( function-Prop
              ( (i : type-I) → is-projective-Cardinal l2 (B i))
              ( function-Prop
                ( (i : type-I) → is-discrete-Cardinal (B i))
                ( function-Prop
                  ( (i : type-I) → merely-decidable-Σ-Cardinal l2 (B i))
                  ( function-Prop
                    ( (i : type-I) → is-discrete-Cardinal (A i))
                    ( function-Prop
                      ( (i : type-I) → merely-decidable-Σ-Cardinal l2 (A i))
                      ( le-complemented-prop-Cardinal
                        ( Σ-Cardinal I A)
                        ( Π-Cardinal I B)))))))))
      ( λ A B H
      is-projective-B is-discrete-B merely-Σ-B is-discrete-A merely-Σ-A →
        binary-tr
          ( le-complemented-Cardinal)
          ( inv (compute-Σ-Cardinal I A))
          ( inv (compute-Π-Cardinal I B))
          ( le-complemented-cardinality-Σ-Π A B H
            ( λ i →
              inv-unit-is-projective-cardinality (B i) (is-projective-B i))
            ( is-discrete-B)
            ( merely-Σ-B)
            ( is-discrete-A)
            ( merely-Σ-A)))
```

### Kőnig's theorem for strict inequality, assuming excluded middle

<!-- TODO: prove `merely-decidable-Σ-Cardinal` from `LEM` -->

```agda
module _
  {l1 l2 : Level}
  (lem : LEM)
  (I : Cardinality-Projective-Set l1 l2)
  (let type-I = type-Cardinality-Projective-Set I)
  where

  le-Σ-Π-Cardinal-LEM :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → le-Cardinal (A i) (B i)) →
    ((i : type-I) → is-projective-Cardinal l2 (B i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (B i)) →
    ((i : type-I) → merely-decidable-Σ-Cardinal l2 (A i)) →
    le-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  le-Σ-Π-Cardinal-LEM =
    apply-twice-ind-Cardinality-Projective-Set I
      ( λ A B →
        set-Prop
          ( function-Prop
            ( (i : type-I) → le-Cardinal (A i) (B i))
            ( function-Prop
              ( (i : type-I) → is-projective-Cardinal l2 (B i))
              ( function-Prop
                ( (i : type-I) → merely-decidable-Σ-Cardinal l2 (B i))
                ( function-Prop
                  ( (i : type-I) → merely-decidable-Σ-Cardinal l2 (A i))
                  ( le-prop-Cardinal
                    (Σ-Cardinal I A) (Π-Cardinal I B)))))))
      ( λ A B H is-projective-B merely-Σ-B merely-Σ-A →
        binary-tr
          ( le-Cardinal)
          ( inv (compute-Σ-Cardinal I A))
          ( inv (compute-Π-Cardinal I B))
          ( le-cardinality-Σ-Π
            ( lem)
            ( I)
            ( λ i j → lem (Id-Prop (set-Cardinality-Projective-Set I) i j))
            ( A)
            ( B)
            ( H)
            ( λ i →
              inv-unit-is-projective-cardinality (B i) (is-projective-B i))
            ( λ i →
              unit-is-discrete-cardinality
                ( B i)
                ( λ x y → lem (Id-Prop (B i) x y)))
            ( merely-Σ-B)
            ( merely-Σ-A)))
```

## Comments

More generally, for every localization `L` contained in `Set` there is an
`L`-modal Kőnig's theorem.

## External links

- [Kőnig's theorem (set theory)](<https://en.wikipedia.org/wiki/K%C5%91nig%27s_theorem_(set_theory)>)
  on Wikipedia
