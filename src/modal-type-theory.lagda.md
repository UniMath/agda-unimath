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
open import foundation.function-extensionality-axiom

module
  modal-type-theory
  (funext : function-extensionality)
  where

open import modal-type-theory.action-on-homotopies-flat-modality funext public
open import modal-type-theory.action-on-identifications-crisp-functions funext public
open import modal-type-theory.action-on-identifications-flat-modality funext public
open import modal-type-theory.crisp-cartesian-product-types funext public
open import modal-type-theory.crisp-coproduct-types funext public
open import modal-type-theory.crisp-dependent-function-types funext public
open import modal-type-theory.crisp-dependent-pair-types funext public
open import modal-type-theory.crisp-function-types funext public
open import modal-type-theory.crisp-identity-types funext public
open import modal-type-theory.crisp-law-of-excluded-middle funext public
open import modal-type-theory.crisp-pullbacks funext public
open import modal-type-theory.crisp-types public
open import modal-type-theory.dependent-universal-property-flat-discrete-crisp-types funext public
open import modal-type-theory.flat-discrete-crisp-types funext public
open import modal-type-theory.flat-modality funext public
open import modal-type-theory.flat-sharp-adjunction funext public
open import modal-type-theory.functoriality-flat-modality funext public
open import modal-type-theory.functoriality-sharp-modality funext public
open import modal-type-theory.sharp-codiscrete-maps funext public
open import modal-type-theory.sharp-codiscrete-types funext public
open import modal-type-theory.sharp-modality funext public
open import modal-type-theory.transport-along-crisp-identifications funext public
open import modal-type-theory.universal-property-flat-discrete-crisp-types funext public
```
