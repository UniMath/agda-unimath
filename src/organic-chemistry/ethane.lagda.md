# Ethane

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module organic-chemistry.ethane
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers funext univalence truncations

open import finite-group-theory.tetrahedra-in-3-space funext univalence truncations

open import foundation.coproduct-types funext univalence truncations
open import foundation.decidable-propositions funext univalence truncations
open import foundation.decidable-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.embeddings funext
open import foundation.empty-types funext univalence truncations
open import foundation.equality-dependent-pair-types funext
open import foundation.identity-types funext
open import foundation.injective-maps funext
open import foundation.propositional-truncations funext univalence
open import foundation.propositions funext univalence
open import foundation.torsorial-type-families funext univalence truncations
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence funext univalence
open import foundation.universe-levels
open import foundation.unordered-pairs funext univalence truncations

open import graph-theory.finite-graphs funext univalence truncations
open import graph-theory.walks-undirected-graphs funext univalence truncations

open import organic-chemistry.alkanes funext univalence truncations
open import organic-chemistry.hydrocarbons funext univalence truncations

open import univalent-combinatorics.2-element-types funext univalence truncations
open import univalent-combinatorics.counting funext univalence truncations
open import univalent-combinatorics.finite-types funext univalence truncations
open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

**Ethane** is the unique alkane with two carbons.

## Definition

```agda
module _
  (t : tetrahedron-in-3-space) (v : vertex-tetrahedron-in-3-space t)
  where

  vertex-ethane-Finite-Type : Finite-Type lzero
  vertex-ethane-Finite-Type = Fin-Finite-Type 2

  vertex-ethane : UU lzero
  vertex-ethane = type-Finite-Type vertex-ethane-Finite-Type

  edge-ethane-Prop : unordered-pair vertex-ethane → Prop lzero
  edge-ethane-Prop p =
    product-Prop
      ( is-in-unordered-pair-Prop p (zero-Fin 1))
      ( is-in-unordered-pair-Prop p (one-Fin 1))

  edge-ethane : unordered-pair vertex-ethane → UU lzero
  edge-ethane p = type-Prop (edge-ethane-Prop p)

  abstract
    is-prop-edge-ethane :
      (p : unordered-pair vertex-ethane) → is-prop (edge-ethane p)
    is-prop-edge-ethane p = is-prop-type-Prop (edge-ethane-Prop p)

  standard-edge-ethane-Prop : (c c' : vertex-ethane) → Prop lzero
  standard-edge-ethane-Prop c c' =
    edge-ethane-Prop (standard-unordered-pair c c')

  standard-edge-ethane : (c c' : vertex-ethane) → UU lzero
  standard-edge-ethane c c' = type-Prop (standard-edge-ethane-Prop c c')

  abstract
    is-prop-standard-edge-ethane :
      (c c' : vertex-ethane) → is-prop (standard-edge-ethane c c')
    is-prop-standard-edge-ethane c c' =
      is-prop-type-Prop (standard-edge-ethane-Prop c c')

  abstract
    is-decidable-edge-ethane-eq-Fin-2 :
      (p : unordered-pair vertex-ethane) →
      type-unordered-pair p ＝ Fin 2 →
      is-decidable (edge-ethane p)
    is-decidable-edge-ethane-eq-Fin-2 p refl with
      is-zero-or-one-Fin-2 (element-unordered-pair p (zero-Fin 1)) |
      is-zero-or-one-Fin-2 (element-unordered-pair p (one-Fin 1))
    ... | inl is-zero | inl is-zero' =
      inr
        ( λ P →
          apply-universal-property-trunc-Prop (pr2 P) empty-Prop
            ( λ where
              ( inl (inr _) , is-one) → neq-inl-inr (inv is-zero ∙ is-one)
              ( inr _ , is-one) → neq-inl-inr (inv is-zero' ∙ is-one)))
    ... | inl is-zero | inr is-one' =
      inl
        ( pair
          ( unit-trunc-Prop (zero-Fin 1 , is-zero))
          ( unit-trunc-Prop (one-Fin 1 , is-one')))
    ... | inr is-one | inl is-zero' =
      inl
        ( pair
          ( unit-trunc-Prop (one-Fin 1 , is-zero'))
          ( unit-trunc-Prop (zero-Fin 1 , is-one)))
    ... | inr is-one | inr is-one' =
      inr
        ( λ P →
          apply-universal-property-trunc-Prop (pr1 P) empty-Prop
            ( λ where
              ( inl (inr _) , is-zero) → neq-inl-inr (inv is-zero ∙ is-one)
              ( inr _ , is-zero) → neq-inl-inr (inv is-zero ∙ is-one')))

  is-decidable-standard-edge-ethane :
    (c c' : vertex-ethane) → is-decidable (standard-edge-ethane c c')
  is-decidable-standard-edge-ethane c c' =
    is-decidable-edge-ethane-eq-Fin-2 (standard-unordered-pair c c') refl

  abstract
    is-finite-edge-ethane :
      (p : unordered-pair vertex-ethane) → is-finite (edge-ethane p)
    is-finite-edge-ethane p =
      apply-universal-property-trunc-Prop
        ( has-two-elements-type-unordered-pair p)
        ( is-finite-Prop (edge-ethane p))
        ( λ e →
          is-finite-is-decidable-Prop
            ( edge-ethane-Prop p)
            ( is-decidable-edge-ethane-eq-Fin-2 p (inv (eq-equiv e))))

  edge-ethane-Finite-Type : unordered-pair vertex-ethane → Finite-Type lzero
  pr1 (edge-ethane-Finite-Type p) = edge-ethane p
  pr2 (edge-ethane-Finite-Type p) = is-finite-edge-ethane p

  finite-graph-ethane : Finite-Undirected-Graph lzero lzero
  pr1 finite-graph-ethane = vertex-ethane-Finite-Type
  pr2 finite-graph-ethane = edge-ethane-Finite-Type

  bonding-ethane :
    (c : vertex-ethane) →
    Σ (vertex-ethane) (λ c' → standard-edge-ethane c c') →
    vertex-tetrahedron-in-3-space t
  bonding-ethane c e = v

  abstract
    is-torsorial-standard-edge-ethane :
      (c : vertex-ethane) → is-torsorial (λ c' → standard-edge-ethane c c')
    pr1 (pr1 (is-torsorial-standard-edge-ethane (inl (inr _)))) = one-Fin 1
    pr1 (pr2 (pr1 (is-torsorial-standard-edge-ethane (inl (inr _))))) =
      unit-trunc-Prop (zero-Fin 1 , refl)
    pr2 (pr2 (pr1 (is-torsorial-standard-edge-ethane (inl (inr _))))) =
      unit-trunc-Prop (one-Fin 1 , refl)
    pr2 (is-torsorial-standard-edge-ethane (inl (inr _))) (inl (inr _) , P) =
      ex-falso
        ( apply-universal-property-trunc-Prop (pr2 P) empty-Prop
          ( λ where
            ( inl (inr _) , is-one) → neq-inl-inr is-one
            ( inr _ , is-one) → neq-inl-inr is-one))
    pr2 (is-torsorial-standard-edge-ethane (inl (inr _))) (inr _ , P) =
      eq-pair-eq-fiber
        ( eq-is-prop
          ( is-prop-edge-ethane
            ( standard-unordered-pair (inl (inr _)) (inr _))))
    pr1 (pr1 (is-torsorial-standard-edge-ethane (inr _))) = zero-Fin 1
    pr1 (pr2 (pr1 (is-torsorial-standard-edge-ethane (inr _)))) =
      unit-trunc-Prop (one-Fin 1 , refl)
    pr2 (pr2 (pr1 (is-torsorial-standard-edge-ethane (inr _)))) =
      unit-trunc-Prop (zero-Fin 1 , refl)
    pr2 (is-torsorial-standard-edge-ethane (inr _)) (inl (inr _) , P) =
      eq-pair-eq-fiber
        ( eq-is-prop
          ( is-prop-edge-ethane
            ( standard-unordered-pair (inr star) (inl (inr star)))))
    pr2 (is-torsorial-standard-edge-ethane (inr _)) (inr _ , P) =
      ex-falso
        ( apply-universal-property-trunc-Prop (pr1 P) empty-Prop
          ( λ where
            ( inl (inr _) , is-zero) → neq-inr-inl is-zero
            ( inr _ , is-zero) → neq-inr-inl is-zero))

  abstract
    is-emb-bonding-ethane : (c : vertex-ethane) → is-emb (bonding-ethane c)
    is-emb-bonding-ethane c =
      is-emb-is-injective
        ( is-set-type-Type-With-Cardinality-ℕ 4 (pr1 t))
        ( is-injective-is-contr (λ e → v) (is-torsorial-standard-edge-ethane c))

  emb-bonding-ethane :
    (c : vertex-ethane) →
    Σ (vertex-ethane) (λ c' → standard-edge-ethane c c') ↪
    vertex-tetrahedron-in-3-space t
  pr1 (emb-bonding-ethane c) = bonding-ethane c
  pr2 (emb-bonding-ethane c) = is-emb-bonding-ethane c

  count-standard-edge-ethane :
    (c c' : vertex-ethane) → count (standard-edge-ethane c c')
  count-standard-edge-ethane c c' =
    count-is-decidable-Prop
      ( standard-edge-ethane-Prop c c')
      ( is-decidable-standard-edge-ethane c c')

  abstract
    number-of-elements-count-standard-edge-ethane-leq-3 :
      (c c' : vertex-ethane) →
      number-of-elements-count (count-standard-edge-ethane c c') ≤-ℕ 3
    number-of-elements-count-standard-edge-ethane-leq-3
      (inl (inr _)) (inl (inr _)) =
      star
    number-of-elements-count-standard-edge-ethane-leq-3
      (inl (inr _)) (inr _) =
      star
    number-of-elements-count-standard-edge-ethane-leq-3
      (inr _) (inl (inr _)) =
      star
    number-of-elements-count-standard-edge-ethane-leq-3
      (inr _) (inr _) = star

  ethane : hydrocarbon lzero lzero
  pr1 ethane = finite-graph-ethane
  pr1 (pr2 ethane) c = t
  pr1 (pr2 (pr2 ethane)) = emb-bonding-ethane
  pr1 (pr2 (pr2 (pr2 ethane))) (inl (inr _)) P =
    apply-universal-property-trunc-Prop (pr2 P) empty-Prop
      ( λ where
        ( inl (inr _) , is-one) → neq-inl-inr is-one
        ( inr _ , is-one) → neq-inl-inr is-one)
  pr1 (pr2 (pr2 (pr2 ethane))) (inr _) P =
    apply-universal-property-trunc-Prop (pr1 P) empty-Prop
      ( λ where
        ( inl (inr _) , is-zero) → neq-inr-inl is-zero
        ( inr _ , is-zero) → neq-inr-inl is-zero)
  pr1 (pr2 (pr2 (pr2 (pr2 ethane)))) c c' =
    concatenate-eq-leq-ℕ 3
      ( inv
        ( compute-number-of-elements-is-finite
          ( count-standard-edge-ethane c c')
          ( is-finite-edge-ethane (standard-unordered-pair c c'))))
      (number-of-elements-count-standard-edge-ethane-leq-3 c c')
  pr2 (pr2 (pr2 (pr2 (pr2 ethane)))) (inl (inr _)) (inl (inr _)) =
    unit-trunc-Prop refl-walk-Undirected-Graph
  pr2 (pr2 (pr2 (pr2 (pr2 ethane)))) (inl (inr _)) (inr _) =
    unit-trunc-Prop
      ( tr
        ( λ x →
          walk-Undirected-Graph
            ( undirected-graph-Finite-Undirected-Graph finite-graph-ethane)
            ( zero-Fin 1)
            ( element-standard-unordered-pair (zero-Fin 1) (one-Fin 1) x))
        ( compute-swap-2-Element-Type
          ( Fin-Type-With-Cardinality-ℕ 2)
          ( zero-Fin 1)
          ( one-Fin 1)
          ( neq-inl-inr))
        ( cons-walk-Undirected-Graph
          ( standard-unordered-pair (zero-Fin 1) (one-Fin 1))
          ( ( unit-trunc-Prop (zero-Fin 1 , refl)) ,
            ( unit-trunc-Prop (one-Fin 1 , refl)))
          { zero-Fin 1}
          ( refl-walk-Undirected-Graph)))
  pr2 (pr2 (pr2 (pr2 (pr2 ethane)))) (inr _) (inl (inr _)) =
    unit-trunc-Prop
      ( tr
        ( λ x →
          walk-Undirected-Graph
            ( undirected-graph-Finite-Undirected-Graph finite-graph-ethane)
            ( one-Fin 1)
            ( element-standard-unordered-pair (one-Fin 1) (zero-Fin 1) x))
        ( compute-swap-2-Element-Type
          ( Fin-Type-With-Cardinality-ℕ 2)
          ( zero-Fin 1)
          ( one-Fin 1)
          ( neq-inl-inr))
        ( cons-walk-Undirected-Graph
          ( standard-unordered-pair (one-Fin 1) (zero-Fin 1))
          ( ( unit-trunc-Prop (one-Fin 1 , refl)) ,
            ( unit-trunc-Prop (zero-Fin 1 , refl)))
          { zero-Fin 1}
          ( refl-walk-Undirected-Graph)))
  pr2 (pr2 (pr2 (pr2 (pr2 ethane)))) (inr _) (inr _) =
    unit-trunc-Prop refl-walk-Undirected-Graph

  is-alkane-ethane : is-alkane-hydrocarbon ethane
  is-alkane-ethane = is-prop-standard-edge-ethane
```
