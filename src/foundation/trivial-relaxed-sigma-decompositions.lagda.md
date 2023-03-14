# Trivial relaxed Σ-Decompositions

```agda
module foundation.trivial-relaxed-sigma-decompositions where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositions
open import foundation.relaxed-sigma-decompositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

## Definitions

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  trivial-Relaxed-Σ-Decomposition :
    Relaxed-Σ-Decomposition l2 l1 A
  pr1 (trivial-Relaxed-Σ-Decomposition) = raise-unit l2
  pr1 (pr2 (trivial-Relaxed-Σ-Decomposition))  = λ _ → A
  pr2 (pr2 (trivial-Relaxed-Σ-Decomposition)) =
    inv-left-unit-law-Σ-is-contr
      ( is-contr-raise-unit)
      ( raise-star)

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Relaxed-Σ-Decomposition l2 l3 A)
  where

  is-trivial-Prop-Relaxed-Σ-Decomposition : Prop l2
  is-trivial-Prop-Relaxed-Σ-Decomposition =
    is-contr-Prop (indexing-type-Relaxed-Σ-Decomposition D)

  is-trivial-Relaxed-Σ-Decomposition : UU l2
  is-trivial-Relaxed-Σ-Decomposition =
    type-Prop is-trivial-Prop-Relaxed-Σ-Decomposition

is-trivial-trivial-inhabited-Relaxed-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-trivial-Relaxed-Σ-Decomposition (trivial-Relaxed-Σ-Decomposition l2 A)
is-trivial-trivial-inhabited-Relaxed-Σ-Decomposition = is-contr-raise-unit

type-trivial-Relaxed-Σ-Decomposition :
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-trivial-Relaxed-Σ-Decomposition {l1} {l2} {l3} {A}=
  type-subtype (is-trivial-Prop-Relaxed-Σ-Decomposition {l1} {l2} {l3} {A})
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Relaxed-Σ-Decomposition l2 l3 A)
  ( is-trivial : is-trivial-Relaxed-Σ-Decomposition D)
  where

  equiv-trivial-is-trivial-Relaxed-Σ-Decomposition :
    equiv-Relaxed-Σ-Decomposition D ( trivial-Relaxed-Σ-Decomposition l4 A)
  pr1 equiv-trivial-is-trivial-Relaxed-Σ-Decomposition =
    ( map-equiv (compute-raise-unit l4) ∘ terminal-map ,
      is-equiv-comp
        ( map-equiv (compute-raise-unit l4))
        ( terminal-map)
        ( is-equiv-terminal-map-is-contr is-trivial)
        ( is-equiv-map-equiv ( compute-raise-unit l4)))
  pr1 (pr2 equiv-trivial-is-trivial-Relaxed-Σ-Decomposition) =
    ( λ x →
      ( ( inv-equiv (matching-correspondence-Relaxed-Σ-Decomposition D)) ∘e
        ( inv-left-unit-law-Σ-is-contr is-trivial x )))
  pr2 (pr2 equiv-trivial-is-trivial-Relaxed-Σ-Decomposition ) a =
    eq-pair-Σ
      ( refl)
      ( inv-map-eq-transpose-equiv
        ( inv-equiv (matching-correspondence-Relaxed-Σ-Decomposition D))
        ( refl))

is-contr-type-trivial-Relaxed-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-contr (type-trivial-Relaxed-Σ-Decomposition {l1} {l2} {l1} {A})
pr1 ( is-contr-type-trivial-Relaxed-Σ-Decomposition {l1} {l2} {A}) =
  ( trivial-Relaxed-Σ-Decomposition l2 A ,
    is-trivial-trivial-inhabited-Relaxed-Σ-Decomposition {l1} {l2} {A})
pr2 ( is-contr-type-trivial-Relaxed-Σ-Decomposition {l1} {l2} {A}) =
   ( λ x →
     eq-type-subtype
       ( is-trivial-Prop-Relaxed-Σ-Decomposition)
       ( inv
         ( eq-equiv-Relaxed-Σ-Decomposition
           ( pr1 x)
           ( trivial-Relaxed-Σ-Decomposition l2 A)
           ( equiv-trivial-is-trivial-Relaxed-Σ-Decomposition (pr1 x) (pr2 x)))))
```
