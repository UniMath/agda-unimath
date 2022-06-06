{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QpropositionalZ45Zextensionality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QsubtypeZ45ZidentityZ45Zprinciple
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZcartesianZ45ZproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QemptyZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZfunctionZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QlogicalZ45Zequivalences
import qualified MAlonzo.Code.Qfoundation.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZemptyZ45Ztype

-- foundation.propositional-extensionality._.is-contr-total-iff
d_is'45'contr'45'total'45'iff_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'iff_14 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv_184
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (\ v2 ->
            coe
              MAlonzo.Code.Qfoundation.QlogicalZ45Zequivalences.du_equiv'45'equiv'45'iff_48))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QsubtypeZ45ZidentityZ45Zprinciple.du_is'45'contr'45'total'45'Eq'45'subtype_30
         (coe
            MAlonzo.Code.Qfoundation.Qpropositions.d_is'45'prop'45'is'45'prop_24
            (coe v0))
         erased
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
            (coe v1)))
-- foundation.propositional-extensionality._.is-equiv-iff-eq
d_is'45'equiv'45'iff'45'eq_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'iff'45'eq_24 ~v0 v1
  = du_is'45'equiv'45'iff'45'eq_24 v1
du_is'45'equiv'45'iff'45'eq_24 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'iff'45'eq_24 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.propositional-extensionality._.propositional-extensionality
d_propositional'45'extensionality_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_propositional'45'extensionality_34 ~v0 v1 v2
  = du_propositional'45'extensionality_34 v1 v2
du_propositional'45'extensionality_34 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_propositional'45'extensionality_34 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v2 ->
         coe
           MAlonzo.Code.Qfoundation.QlogicalZ45Zequivalences.du_iff'45'eq_10)
      (coe du_is'45'equiv'45'iff'45'eq_24 v0 v1)
-- foundation.propositional-extensionality._.eq-iff'
d_eq'45'iff''_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'iff''_48 = erased
-- foundation.propositional-extensionality._.eq-iff
d_eq'45'iff_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'iff_58 = erased
-- foundation.propositional-extensionality._.eq-equiv-Prop
d_eq'45'equiv'45'Prop_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv'45'Prop_72 = erased
-- foundation.propositional-extensionality.is-set-UU-Prop
d_is'45'set'45'UU'45'Prop_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'UU'45'Prop_78 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'equiv_196
      (coe du_propositional'45'extensionality_34 (coe v1) (coe v2))
      (MAlonzo.Code.Qfoundation.QlogicalZ45Zequivalences.d_is'45'prop'45'logical'45'equivalence_66
         (coe v0) (coe v0) (coe v1) (coe v2))
-- foundation.propositional-extensionality.UU-Prop-Set
d_UU'45'Prop'45'Set_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_UU'45'Prop'45'Set_88 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'set'45'UU'45'Prop_78 (coe v0))
-- foundation.propositional-extensionality.is-contr-total-true-Prop
d_is'45'contr'45'total'45'true'45'Prop_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'true'45'Prop_98 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv_184
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                    (coe
                       MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_equiv'45'universal'45'property'45'contr_286
                       (coe MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_raise'45'star_34)
                       (coe v0))
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZcartesianZ45ZproductZ45Ztypes.du_right'45'unit'45'law'45'prod'45'is'45'contr_116
                       (coe
                          MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_is'45'contr'45'Π_16
                          (coe v0) (coe v0)
                          (coe
                             (\ v2 ->
                                coe
                                  MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                                  (coe
                                     MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_is'45'prop'45'raise'45'unit_98)
                                  (coe
                                     MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_raise'45'star_34)))))))))
      (coe
         d_is'45'contr'45'total'45'iff_14 (coe v0)
         (coe
            MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_raise'45'unit'45'Prop_104))
-- foundation.propositional-extensionality.is-contr-total-false-Prop
d_is'45'contr'45'total'45'false'45'Prop_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'false'45'Prop_112 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv_184
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
                       (coe
                          MAlonzo.Code.Qfoundation.QfunctorialityZ45ZfunctionZ45Ztypes.du_equiv'45'postcomp_164
                          (coe
                             MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50)))
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZcartesianZ45ZproductZ45Ztypes.du_left'45'unit'45'law'45'prod'45'is'45'contr_136
                       (coe
                          MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZemptyZ45Ztype.du_universal'45'property'45'empty'45'is'45'empty_78
                          v0 erased))))))
      (coe
         d_is'45'contr'45'total'45'iff_14 (coe v0)
         (coe
            MAlonzo.Code.Qfoundation.QemptyZ45Ztypes.du_raise'45'empty'45'Prop_76))
