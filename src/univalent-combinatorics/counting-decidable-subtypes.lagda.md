# Counting the elements of decidable subtypes

```agda
open import foundation.function-extensionality-axiom

module
  univalent-combinatorics.counting-decidable-subtypes
  (funext : function-extensionality)
  where

open import foundation.decidable-subtypes funext public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types funext
open import foundation.coproduct-types funext
open import foundation.decidable-embeddings funext
open import foundation.decidable-types funext
open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.equivalences funext
open import foundation.fibers-of-maps funext
open import foundation.function-types funext
open import foundation.functoriality-coproduct-types funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.identity-types funext
open import foundation.propositional-maps funext
open import foundation.propositional-truncations funext
open import foundation.propositions funext
open import foundation.subtypes funext
open import foundation.type-arithmetic-coproduct-types funext
open import foundation.type-arithmetic-empty-type funext
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting funext
open import univalent-combinatorics.decidable-propositions funext
open import univalent-combinatorics.finite-types funext
open import univalent-combinatorics.standard-finite-types funext
```

</details>

## Properties

### The elements of a decidable subtype of a type equipped with a counting can be counted

```agda
abstract
  count-decidable-subtype' :
    {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) →
    (k : ℕ) (e : Fin k ≃ X) → count (type-decidable-subtype P)
  count-decidable-subtype' P zero-ℕ e =
    count-is-empty
      ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl ∘ pr1)
  count-decidable-subtype' P (succ-ℕ k) e
    with is-decidable-decidable-subtype P (map-equiv e (inr star))
  ... | inl p =
    count-equiv
      ( equiv-Σ (is-in-decidable-subtype P) e (λ x → id-equiv))
      ( count-equiv'
        ( right-distributive-Σ-coproduct
          ( Fin k)
          ( unit)
          ( λ x → is-in-decidable-subtype P (map-equiv e x)))
        ( pair
          ( succ-ℕ
            ( number-of-elements-count
              ( count-decidable-subtype'
                ( λ x → P (map-equiv e (inl x)))
                ( k)
                ( id-equiv))))
          ( equiv-coproduct
            ( equiv-count
              ( count-decidable-subtype'
                ( λ x → P (map-equiv e (inl x)))
                ( k)
                ( id-equiv)))
            ( equiv-is-contr
              ( is-contr-unit)
              ( is-contr-Σ
                ( is-contr-unit)
                ( star)
                ( is-proof-irrelevant-is-prop
                  ( is-prop-is-in-decidable-subtype P
                    ( map-equiv e (inr star)))
                  ( p)))))))
  ... | inr f =
    count-equiv
      ( equiv-Σ (is-in-decidable-subtype P) e (λ x → id-equiv))
      ( count-equiv'
        ( right-distributive-Σ-coproduct
          ( Fin k)
          ( unit)
          ( λ x → is-in-decidable-subtype P (map-equiv e x)))
        ( count-equiv'
          ( right-unit-law-coproduct-is-empty
            ( Σ ( Fin k)
                ( λ x → is-in-decidable-subtype P (map-equiv e (inl x))))
            ( Σ ( unit)
                ( λ x → is-in-decidable-subtype P (map-equiv e (inr x))))
            ( λ where (star , p) → f p))
          ( count-decidable-subtype'
            ( λ x → P (map-equiv e (inl x)))
            ( k)
            ( id-equiv))))

count-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) →
  (count X) → count (type-decidable-subtype P)
count-decidable-subtype P e =
  count-decidable-subtype' P
    ( number-of-elements-count e)
    ( equiv-count e)
```

### The elements in the domain of a decidable embedding can be counted if the elements of the codomain can be counted

```agda
count-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ᵈ Y) → count Y → count X
count-decidable-emb f e =
  count-equiv
    ( equiv-total-fiber (map-decidable-emb f))
    ( count-decidable-subtype (decidable-subtype-decidable-emb f) e)
```

### If the elements of a subtype of a type equipped with a counting can be counted, then the subtype is decidable

```agda
is-decidable-count-subtype :
  {l1 l2 : Level} {X : UU l1} (P : subtype l2 X) → count X →
  count (type-subtype P) → (x : X) → is-decidable (type-Prop (P x))
is-decidable-count-subtype P e f x =
  is-decidable-count
    ( count-equiv
      ( equiv-fiber-pr1 (type-Prop ∘ P) x)
      ( count-decidable-subtype
        ( λ y →
          pair
            ( Id (pr1 y) x)
            ( pair
              ( is-set-count e (pr1 y) x)
              ( has-decidable-equality-count e (pr1 y) x)))
        ( f)))
```

### If a subtype of a type equipped with a counting is finite, then its elements can be counted

```agda
count-type-subtype-is-finite-type-subtype :
  {l1 l2 : Level} {A : UU l1} (e : count A) (P : subtype l2 A) →
  is-finite (type-subtype P) → count (type-subtype P)
count-type-subtype-is-finite-type-subtype {l1} {l2} {A} e P f =
  count-decidable-subtype
    ( λ x → pair (type-Prop (P x)) (pair (is-prop-type-Prop (P x)) (d x)))
    ( e)
  where
  d : (x : A) → is-decidable (type-Prop (P x))
  d x =
    apply-universal-property-trunc-Prop f
      ( is-decidable-Prop (P x))
      ( λ g → is-decidable-count-subtype P e g x)
```

### For any embedding `B ↪ A` into a type `A` equipped with a counting, if `B` is finite then its elements can be counted

```agda
count-domain-emb-is-finite-domain-emb :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  is-finite B → count B
count-domain-emb-is-finite-domain-emb e f H =
  count-equiv
    ( equiv-total-fiber (map-emb f))
    ( count-type-subtype-is-finite-type-subtype e
      ( λ x → pair (fiber (map-emb f) x) (is-prop-map-emb f x))
      ( is-finite-equiv'
        ( equiv-total-fiber (map-emb f))
        ( H)))
```
