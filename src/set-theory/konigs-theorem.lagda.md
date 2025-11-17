# Kőnig's theorem

```agda
module set-theory.konigs-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.nonsurjective-maps
open import foundation.projective-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import set-theory.cardinality-projective-sets
open import set-theory.cardinals
open import set-theory.dependent-products-cardinals
open import set-theory.dependent-sums-cardinals
open import set-theory.strict-indexed-inequality-cardinals
```

</details>

## Idea

{{#concept "Kőnig's theorem" WD="König's theorem" WDID=Q1077462 Disambiguation="for cardinals" Agda=Königs-Theorem}}
states that for any pair of families of [cardinals](set-theory.cardinals.md) $A$
and $B$ over $I$ such that $Aᵢ < Bᵢ$ for all $i$, we have that
$$∑_{i:I}Aᵢ < ∏_{i:I}Bᵢ.$$

In constructive mathematics we have to be more mindful of our statements. Here
$I$ is any
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
    (H : (i : I) → (f : A i → B i) → is-nonsurjective f)
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

  cardinality-Königs-Theorem' :
    (A B : type-Set I → Set l2) →
    ((i : type-Set I) → le-indexed-cardinality' (A i) (B i)) →
    le-indexed-cardinality' (Σ-Set I A) (Π-Set I B)
  cardinality-Königs-Theorem' A B p =
    ( is-projective-I (type-Set ∘ B) (pr1 ∘ p) ,
      is-nonsurjective-map-Σ-Π-is-projective-base' is-projective-I (pr2 ∘ p))

  cardinality-Königs-Theorem :
    (A B : type-Set I → Set l2) →
    ((i : type-Set I) → le-indexed-cardinality (A i) (B i)) →
    le-indexed-cardinality (Σ-Set I A) (Π-Set I B)
  cardinality-Königs-Theorem A B p =
    unit-le-indexed-cardinality
      ( Σ-Set I A)
      ( Π-Set I B)
      ( cardinality-Königs-Theorem' A B
        ( λ i → inv-unit-le-indexed-cardinality (A i) (B i) (p i)))

module _
  {l1 l2 : Level}
  (I : Cardinality-Projective-Set l1 l2)
  (let type-I = type-Cardinality-Projective-Set I)
  (let set-I = set-Cardinality-Projective-Set I)
  where

  Königs-Theorem :
    (A B : type-I → Cardinal l2) →
    ((i : type-I) → le-indexed-Cardinal (A i) (B i)) →
    le-indexed-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B)
  Königs-Theorem =
    apply-twice-ind-Cardinality-Projective-Set I
      ( λ A B →
        set-Prop
          ( function-Prop
            ( (i : type-I) → le-indexed-Cardinal (A i) (B i))
            ( le-indexed-prop-Cardinal (Σ-Cardinal I A) (Π-Cardinal I B))))
      ( λ A B p →
        binary-tr le-indexed-Cardinal
          ( inv (compute-Σ-Cardinal I A))
          ( inv (compute-Π-Cardinal I B))
          ( cardinality-Königs-Theorem
            ( set-I)
            ( is-projective-Cardinality-Projective-Set I)
            ( A)
            ( B)
            ( p)))
```

## Comments

More generally, for every localization `L` contained in `Set` there is an
`L`-modal Kőnig's theorem.

## External links

- [Kőnig's theorem (set theory)](<https://en.wikipedia.org/wiki/K%C5%91nig%27s_theorem_(set_theory)>)
  on Wikipedia
