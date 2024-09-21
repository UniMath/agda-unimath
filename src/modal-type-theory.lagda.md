# Modal type theory

```agda
{-# OPTIONS --cohesion --flat-split #-}
```

Modal type theory is the study of type theory extended with syntactic _modal_
operators. These are operations on types that increase the expressivity of the
type theory in some way.

In this namespace, we consider modal extensions of Martin-Löf type theory with a
[flat modality](modal-type-theory.flat-modality.md) `♭`,
[sharp modality](modal-type-theory.sharp-modality.md) `♯`, and more to come. The
[adjoint pair of modalities](modal-type-theory.flat-sharp-adjunction.md)
`♭ ⊣ ＃` display a structure on all types referred to as _spatial_, or
_cohesive_ structure.

- To read more, continue to [crisp types](modal-type-theory.crisp-types.md).

## Modules in the modal type theory namespace

```agda
module modal-type-theory where

open import modal-type-theory.action-on-homotopies-flat-modality public
open import modal-type-theory.action-on-identifications-crisp-functions public
open import modal-type-theory.action-on-identifications-flat-modality public
open import modal-type-theory.crisp-cartesian-product-types public
open import modal-type-theory.crisp-coproduct-types public
open import modal-type-theory.crisp-dependent-function-types public
open import modal-type-theory.crisp-dependent-pair-types public
open import modal-type-theory.crisp-function-types public
open import modal-type-theory.crisp-identity-types public
open import modal-type-theory.crisp-law-of-excluded-middle public
open import modal-type-theory.crisp-pullbacks public
open import modal-type-theory.crisp-types public
open import modal-type-theory.dependent-universal-property-flat-discrete-crisp-types public
open import modal-type-theory.flat-discrete-crisp-types public
open import modal-type-theory.flat-modality public
open import modal-type-theory.flat-sharp-adjunction public
open import modal-type-theory.functoriality-flat-modality public
open import modal-type-theory.functoriality-sharp-modality public
open import modal-type-theory.sharp-codiscrete-maps public
open import modal-type-theory.sharp-codiscrete-types public
open import modal-type-theory.sharp-modality public
open import modal-type-theory.transport-along-crisp-identifications public
open import modal-type-theory.universal-property-flat-discrete-crisp-types public
```
