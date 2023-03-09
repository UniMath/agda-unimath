# Decidable propositions

```agda
module foundation.decidable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.decidable-propositions public

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.small-types
open import foundation.subtypes
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A decidable proposition is a proposition that has a decidable underlying type.

## Properties

### The forgetful map from decidable propositions to propositions is an embedding

```agda
is-emb-prop-decidable-Prop : {l : Level} → is-emb (prop-decidable-Prop {l})
is-emb-prop-decidable-Prop =
  is-emb-tot
    ( λ X →
      is-emb-inclusion-subtype
        ( λ H → pair (is-decidable X) (is-prop-is-decidable H)))

emb-prop-decidable-Prop :
  {l : Level} → decidable-Prop l ↪ Prop l
pr1 emb-prop-decidable-Prop = prop-decidable-Prop
pr2 emb-prop-decidable-Prop = is-emb-prop-decidable-Prop
```

### The type of decidable propositions in universe level `l` is equivalent to the type of booleans

```agda
module _
  {l : Level}
  where

  split-decidable-Prop :
    decidable-Prop l ≃
    ((Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q))))
  split-decidable-Prop =
    ( left-distributive-Σ-coprod (Prop l) (λ Q → pr1 Q) (λ Q → ¬ (pr1 Q))) ∘e
    ( inv-assoc-Σ (UU l) is-prop (λ X → is-decidable (pr1 X)))

  map-equiv-bool-decidable-Prop' :
    (Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q))) →
    bool
  map-equiv-bool-decidable-Prop' (inl x) = true
  map-equiv-bool-decidable-Prop' (inr x) = false

  map-inv-equiv-bool-decidable-Prop' :
    bool →
    (Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q)))
  map-inv-equiv-bool-decidable-Prop' true =
    inl (pair (raise-unit-Prop l) raise-star)
  map-inv-equiv-bool-decidable-Prop' false =
    inr (pair (raise-empty-Prop l) is-empty-raise-empty)

  issec-map-inv-equiv-bool-decidable-Prop' :
    (map-equiv-bool-decidable-Prop' ∘ map-inv-equiv-bool-decidable-Prop') ~ id
  issec-map-inv-equiv-bool-decidable-Prop' true = refl
  issec-map-inv-equiv-bool-decidable-Prop' false = refl

  isretr-map-inv-equiv-bool-decidable-Prop' :
    (map-inv-equiv-bool-decidable-Prop' ∘ map-equiv-bool-decidable-Prop') ~ id
  isretr-map-inv-equiv-bool-decidable-Prop' (inl x) =
    ap inl (eq-is-contr is-contr-total-true-Prop)
  isretr-map-inv-equiv-bool-decidable-Prop' (inr x) =
    ap inr (eq-is-contr is-contr-total-false-Prop)

  is-equiv-map-equiv-bool-decidable-Prop' :
    is-equiv map-equiv-bool-decidable-Prop'
  is-equiv-map-equiv-bool-decidable-Prop' =
    is-equiv-has-inverse
      map-inv-equiv-bool-decidable-Prop'
      issec-map-inv-equiv-bool-decidable-Prop'
      isretr-map-inv-equiv-bool-decidable-Prop'

  equiv-bool-decidable-Prop' :
    ((Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q)))) ≃
    bool
  pr1 equiv-bool-decidable-Prop' = map-equiv-bool-decidable-Prop'
  pr2 equiv-bool-decidable-Prop' = is-equiv-map-equiv-bool-decidable-Prop'

  equiv-bool-decidable-Prop : decidable-Prop l ≃ bool
  equiv-bool-decidable-Prop = equiv-bool-decidable-Prop' ∘e split-decidable-Prop

  abstract
    compute-equiv-bool-decidable-Prop :
      (P : decidable-Prop l) →
      type-decidable-Prop P ≃ (map-equiv equiv-bool-decidable-Prop P ＝ true)
    compute-equiv-bool-decidable-Prop (pair P (pair H (inl p))) =
      equiv-is-contr
        ( is-proof-irrelevant-is-prop H p)
        ( is-proof-irrelevant-is-prop (is-set-bool true true) refl)
    compute-equiv-bool-decidable-Prop (pair P (pair H (inr np))) =
      equiv-is-empty np neq-false-true-bool
```

### Types of decidable propositions of any universe level are equivalent

```agda
equiv-universes-decidable-Prop : (l l' : Level) →
  decidable-Prop l ≃ decidable-Prop l'
equiv-universes-decidable-Prop l l' =
  inv-equiv equiv-bool-decidable-Prop ∘e equiv-bool-decidable-Prop

iff-universes-decidable-Prop : (l l' : Level) (P : decidable-Prop l) →
  ( prop-decidable-Prop P ⇔
    prop-decidable-Prop (map-equiv (equiv-universes-decidable-Prop l l') P))
pr1 (iff-universes-decidable-Prop l l' P) p =
  map-inv-equiv
    ( compute-equiv-bool-decidable-Prop
      ( map-equiv (equiv-universes-decidable-Prop l l') P))
    ( tr
      ( λ e → map-equiv e (map-equiv equiv-bool-decidable-Prop P) ＝ true)
      ( inv (right-inverse-law-equiv equiv-bool-decidable-Prop))
      ( map-equiv (compute-equiv-bool-decidable-Prop P) p))
pr2 (iff-universes-decidable-Prop l l' P) p =
  map-inv-equiv
    ( compute-equiv-bool-decidable-Prop P)
    ( tr
      ( λ e → map-equiv e (map-equiv equiv-bool-decidable-Prop P) ＝ true)
      ( right-inverse-law-equiv equiv-bool-decidable-Prop)
      ( map-equiv
        ( compute-equiv-bool-decidable-Prop
          ( map-equiv (equiv-universes-decidable-Prop l l') P))
        ( p)))
```

### The type of decidable propositions in any universe is a set

```agda
is-set-decidable-Prop : {l : Level} → is-set (decidable-Prop l)
is-set-decidable-Prop {l} =
  is-set-equiv bool equiv-bool-decidable-Prop is-set-bool
```

### Extensionality of decidable propositions

```agda
module _
  {l : Level} (P Q : decidable-Prop l)
  where

  extensionality-decidable-Prop :
    (P ＝ Q) ≃ (type-decidable-Prop P ↔ type-decidable-Prop Q)
  extensionality-decidable-Prop =
    ( propositional-extensionality
      ( prop-decidable-Prop P)
      ( prop-decidable-Prop Q)) ∘e
    ( equiv-ap-emb emb-prop-decidable-Prop)

  iff-eq-decidable-Prop :
    P ＝ Q → type-decidable-Prop P ↔ type-decidable-Prop Q
  iff-eq-decidable-Prop = map-equiv extensionality-decidable-Prop

  eq-iff-decidable-Prop :
    (type-decidable-Prop P → type-decidable-Prop Q) →
    (type-decidable-Prop Q → type-decidable-Prop P) → P ＝ Q
  eq-iff-decidable-Prop f g =
    map-inv-equiv extensionality-decidable-Prop (pair f g)
```

### The type of decidable propositions in any universe is small

```agda
abstract
  is-small-decidable-Prop :
    (l1 l2 : Level) → is-small l2 (decidable-Prop l1)
  pr1 (is-small-decidable-Prop l1 l2) = raise l2 bool
  pr2 (is-small-decidable-Prop l1 l2) =
    compute-raise l2 bool ∘e equiv-bool-decidable-Prop
```

### Decidable propositions have a count

```agda
count-is-decidable-Prop :
    {l : Level} (P : Prop l) →
    is-decidable (type-Prop P) → count (type-Prop P)
count-is-decidable-Prop P (inl x) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) x)
count-is-decidable-Prop P (inr x) =
  count-is-empty x
```

### Decidable propositions are finite

```agda
abstract
  is-finite-is-decidable-Prop :
    {l : Level} (P : Prop l) →
    is-decidable (type-Prop P) → is-finite (type-Prop P)
  is-finite-is-decidable-Prop P x = is-finite-count (count-is-decidable-Prop P x)
```

### The type of decidable propositions of any universe level is finite

```agda
is-finite-decidable-Prop : {l : Level} → is-finite (decidable-Prop l)
is-finite-decidable-Prop {l} =
  is-finite-equiv' equiv-bool-decidable-Prop is-finite-bool

decidable-Prop-𝔽 : (l : Level) → 𝔽 (lsuc l)
pr1 (decidable-Prop-𝔽 l) = decidable-Prop l
pr2 (decidable-Prop-𝔽 l) = is-finite-decidable-Prop
```

### The negation of a decidable proposition is a decidable proposition

```agda
neg-decidable-Prop :
  {l : Level} → decidable-Prop l → decidable-Prop l
pr1 (neg-decidable-Prop P) = ¬ (type-decidable-Prop P)
pr1 (pr2 (neg-decidable-Prop P)) = is-prop-neg
pr2 (pr2 (neg-decidable-Prop P)) =
  is-decidable-neg (is-decidable-type-decidable-Prop P)
```
