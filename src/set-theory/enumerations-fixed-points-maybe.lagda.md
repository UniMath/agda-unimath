# Enumerations by fixed points of the maybe-monad

```agda
module set-theory.enumerations-fixed-points-maybe where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.type-arithmetic-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.functoriality-propositional-truncation
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.isolated-elements
open import foundation.precomposition-functions
open import foundation.split-surjective-maps
open import foundation.empty-types
open import foundation.coalgebras-maybe
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.extremally-isolated-elements
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retracts-of-types
open import foundation.inhabited-types
open import foundation.sets
open import lists.shifting-sequences
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a type `α`, recall that an `α`-[enumeration](set-theory.enumerations.md)
on another type `X` is a [surjection](foundation.surjective-maps.md)
`α ↠ Maybe X`. When `α` is a [fixed point](foundation.fixed-points.md), then
this condition is equivalent to the following

1. There is a surjection `α ↠ X` or `X` is [empty](foundation.empty-types.md).
2. There is a [decidable subtype](foundation.decidable-subtypes.md) `β` of `α`
   and a surjection `β ↠ X`.

## Properties

### Directly α-enumerable types are α-enumerable

```agda
  -- abstract
  --   is-enumerable-is-directly-enumerable :
  --     (α ≃ Maybe α) → is-directly-enumerable α X → is-enumerable α X
  --   is-enumerable-is-directly-enumerable μ H =
  --     apply-universal-property-trunc-Prop H
  --       ( is-enumerable-Prop α X)
  --       ( λ (f , F) →
  --         unit-trunc-Prop
  --         ( ( λ i →
  --             map-coproduct
  --               ( λ np → rec-coproduct f (point x₀) (map-equiv μ i))
  --               ( λ nnp → star)
  --               ( is-decidable-is-not-exception-Maybe (map-equiv μ i))) ,
  --           λ where
  --           (inl x) → {!    !}
  --           (inr _) →
  --             unit-trunc-Prop
  --               ( map-inv-equiv μ exception-Maybe ,
  --                 ( equational-reasoning
  --                   {! map-coproduct (λ np → rec-coproduct f (λ x₁ → x₀) (pr1 μ (map-inv-equiv μ (inr star)))) (λ nnp → star) (is-decidable-is-not-exception-Maybe (pr1 μ (map-inv-equiv μ (inr star)))) !}
  --                   ＝ {!   !} by {!   !}
  --                   ＝ inr x by {!   !}))))
  --           -- -- ( ( λ where
  --           -- --     zero → inr star
  --           -- --     (succ n) → inl ((shift a (pr1 P)) n)) ,
  --           --   ( λ where
  --           --     ( inl x) →
  --           --       apply-universal-property-trunc-Prop (pr2 P x)
  --           --         ( trunc-Prop (fiber _ (inl x)))
  --           --         ( λ (n , p) →
  --           --           unit-trunc-Prop ?)
  --           --             -- ( succ (succ n) , ap inl p))
  --           --     ( inr star) → unit-trunc-Prop (zero , refl))))
```

### The two definitions of α-enumeration are equivalent

First, we will prove `enumeration α X → decidable-subprojection l2 α X`.

```agda
module _
  {l1 l2 : Level} {α : UU l1} {X : UU l2}
  where

  decidable-subprojection-enumeration :
    enumeration α X → decidable-subprojection l2 α X
  pr1 (pr1 (decidable-subprojection-enumeration (f , H)) n) =
    f n ≠ inr star
  pr1 (pr2 (pr1 (decidable-subprojection-enumeration (f , H)) n)) =
    is-prop-neg
  pr2 (pr2 (pr1 (decidable-subprojection-enumeration (f , H)) n)) =
    is-decidable-is-not-exception-Maybe (f n)
  pr1 (pr2 (decidable-subprojection-enumeration (f , H))) (n , p) =
    value-is-not-exception-Maybe (f n) p
  pr2 (pr2 (decidable-subprojection-enumeration (f , H))) x =
    apply-universal-property-trunc-Prop (H (inl x))
      ( trunc-Prop (fiber _ x))
      ( λ (n , p) →
        unit-trunc-Prop
          ( ( n , is-not-exception-is-value-Maybe (f n) (x , inv p)) ,
            ( is-injective-inl
              ( ( eq-is-not-exception-Maybe
                ( f n)
                ( is-not-exception-is-value-Maybe
                  ( f n) (x , inv p))) ∙
              ( p)))))

  is-enumerable'-is-enumerable :
    is-enumerable α X → is-enumerable' l2 α X
  is-enumerable'-is-enumerable H =
    apply-universal-property-trunc-Prop H
      ( is-enumerable-Prop' l2 α X)
      ( unit-trunc-Prop ∘ decidable-subprojection-enumeration)
```

Second, we prove `decidable-subprojection l2 α X → enumeration α X`, assuming
that α is a fixed point of the `Maybe` monad.

```agda
cases-map-decidable-subtype :
  {l1 l2 : Level} (α : UU l1) (X : UU l2) →
  ( P : decidable-subtype l2 α) →
  ( f : type-decidable-subtype P → X) →
  ( (n : α) → is-decidable (pr1 (P n)) → Maybe X)
cases-map-decidable-subtype α X P f n (inl x) = inl (f (n , x))
cases-map-decidable-subtype α X P f n (inr x) = inr star

-- module _
--   {l1 l2 : Level} (α : UU l1)
--   (M : coalgebra-structure-Maybe α)
--   (X : UU l2)
--   (P : decidable-subtype l2 α)
--   (f : type-decidable-subtype P → X)
--   where

--   shift-decidable-subtype : decidable-subtype l2 α
--   shift-decidable-subtype = {!   !}
  -- shift-decidable-subtype zero =
  --   ( raise-empty l2) ,
  --   ( is-prop-raise-empty , inr (is-empty-raise-empty))
  -- shift-decidable-subtype (succ n) = P n

--   map-shift-decidable-subtype :
--     type-decidable-subtype shift-decidable-subtype → X
--   map-shift-decidable-subtype (zero , map-raise ())
--   map-shift-decidable-subtype (succ n , p) = f (n , p)

--   map-enumeration-decidable-subprojection : α → Maybe X
--   map-enumeration-decidable-subprojection n =
--     cases-map-decidable-subtype
--       ( X)
--       ( shift-decidable-subtype)
--       ( map-shift-decidable-subtype)
--       ( n)
--       (pr2 (pr2 (shift-decidable-subtype n)))

--   abstract
--     is-surjective-map-enumeration-decidable-subprojection :
--       ( is-surjective f) →
--       ( is-surjective map-enumeration-decidable-subprojection)
--     is-surjective-map-enumeration-decidable-subprojection H (inl x) =
--       ( apply-universal-property-trunc-Prop (H x)
--         ( trunc-Prop (fiber map-enumeration-decidable-subprojection (inl x)))
--         ( λ where
--           ( ( n , s) , refl) →
--             unit-trunc-Prop
--               ( ( succ n) ,
--                 ( ap
--                   ( cases-map-decidable-subtype X
--                     ( shift-decidable-subtype)
--                     ( map-shift-decidable-subtype)
--                     (succ n))
--                   ( pr1
--                     ( is-prop-is-decidable (pr1 (pr2 (P n)))
--                       ( pr2 (pr2 (P n)))
--                       ( inl s)))))))
--     is-surjective-map-enumeration-decidable-subprojection H (inr star) =
--       ( unit-trunc-Prop (0 , refl))

-- module _
--   {l : Level} (X : Set l)
--   where

--   enumeration-decidable-subprojection :
--     decidable-subprojection X → enumeration X
--   enumeration-decidable-subprojection (P , (f , H)) =
--     ( map-enumeration-decidable-subprojection X P f) ,
--     ( is-surjective-map-enumeration-decidable-subprojection X P f H)

--   is-enumerable-is-enumerable' :
--     is-enumerable' X → is-enumerable X
--   is-enumerable-is-enumerable' H =
--     apply-universal-property-trunc-Prop H
--       ( is-enumerable-Prop X)
--       ( λ D →
--         ( unit-trunc-Prop (enumeration-decidable-subprojection D)))
```

### The type α is α-enumerable when α is a `Maybe`-fixed point

```text
abstract
  is-enumerable : is-enumerable α α
  is-enumerable =
    unit-trunc-Prop
      ( ( λ where
          zero → inr star
          (succ n) → inl n) ,
        ( λ where
          ( inl n) → unit-trunc-Prop (succ n , refl)
          ( inr star) → unit-trunc-Prop (zero , refl)))
```

### Enumerable types are closed under coproducts

```text
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  is-enumerable-coproduct :
    is-enumerable X → is-enumerable Y → is-enumerable (coproduct-Set X Y)
  is-enumerable-coproduct H H' =
    apply-twice-universal-property-trunc-Prop H' H
      ( is-enumerable-Prop (coproduct-Set X Y))
      ( λ h' h →
        ( unit-trunc-Prop
          ( pair
            ( map-maybe-coproduct ∘
              ( map-coproduct (pr1 h) (pr1 h') ∘ map-to+α))
            ( is-surjective-comp
              ( is-surjective-map-maybe-coproduct)
              ( is-surjective-comp
                ( is-surjective-map-coproduct (pr2 h) (pr2 h'))
                ( is-surjective-is-equiv (is-equiv-map-to+α)))))))
```

### Enumerable types are closed under products

```text
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  is-enumerable-product :
    is-enumerable X → is-enumerable Y → is-enumerable (product-Set X Y)
  is-enumerable-product H H' =
    apply-twice-universal-property-trunc-Prop H' H
      ( is-enumerable-Prop (product-Set X Y))
      ( λ h' h →
        ( unit-trunc-Prop
          ( pair
            ( map-maybe-product ∘
              ( map-product (pr1 h) (pr1 h') ∘ map-to-ℕ×ℕ))
            ( is-surjective-comp
              ( is-surjective-map-maybe-product)
              ( is-surjective-comp
                ( is-surjective-map-product (pr2 h) (pr2 h'))
                ( is-surjective-is-equiv (is-equiv-map-to-ℕ×ℕ)))))))
```

### Countable types are enumerable

> TODO: use that ℕ is the least fixed point of `Maybe`.
